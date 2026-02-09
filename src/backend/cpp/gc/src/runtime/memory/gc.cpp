#include "gc.h"

#include "allocator.h"
#include "threadinfo.h"
#include "decsprcsr.h"
#include "../support/qsort.h"

#define METADATA_SEG_SIZE(P) (P->entrycount * sizeof(MetaData)) 

#ifdef ALLOC_DEBUG_CANARY
#define GET_SLOT_START_FROM_OFFSET(OFF, P) \
	(OFF - sizeof(PageInfo) - METADATA_SEG_SIZE(P) - ALLOC_DEBUG_CANARY_SIZE) 
#else 
#define GET_SLOT_START_FROM_OFFSET(OFF, P) \
	(OFF - sizeof(PageInfo) - METADATA_SEG_SIZE(P)) 
#endif

static void walkPointerMaskForDecrements(__CoreGC::TypeInfoBase* typeinfo, 
	void** slots, ArrayList<void*>& list) noexcept;
static void updatePointers(void** slots, __CoreGC::TypeInfoBase* typeinfo, 
	BSQMemoryTheadLocalInfo& tinfo) noexcept;
static void walkPointerMaskForMarking(BSQMemoryTheadLocalInfo& tinfo, 
	__CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept; 

static inline void pushPendingDecs(void* obj, ArrayList<void*>& list)
{
    // Keep pointed to roots alive
	MetaData* m = GC_GET_META_DATA_ADDR(obj); 
	if(GC_IS_ROOT(m)) {
		// It's a root so still alive, but needs rc update
		if(GC_REF_COUNT(m) > 0) {
			DEC_REF_COUNT(m);	
		}
		return ;
    }

    list.push_back(obj);
}

// A simple two pointer walk of sets stored based on address to determine
// whether a root was droped from the previous set
static void computeDeadRootsForDecrement(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    qsort(tinfo.roots, 0, tinfo.roots_count - 1, tinfo.roots_count);

	// TODO we may be interested in using a separate mtx for thdcnt decs/incs
	std::lock_guard lk(g_gcrefctlock);
    
    int32_t roots_idx = 0, oldroots_idx = 0;
	while(oldroots_idx < tinfo.old_roots_count) {
        void* cur_oldroot = tinfo.old_roots[oldroots_idx];
        void* cur_root = roots_idx < tinfo.roots_count ? 
			tinfo.roots[roots_idx] : static_cast<uint8_t*>(cur_oldroot) + 1;
        if(cur_root < cur_oldroot) {
            // New root in current
            roots_idx++;
        } 
        else if(cur_root > cur_oldroot) { 
             // Was dropped from old roots	
        	MetaData* m = GC_GET_META_DATA_ADDR(cur_oldroot);  
			GC_DROP_ROOT_REF(m);
			if(GC_REF_COUNT(m) == 0 && !GC_IS_ROOT(m)) {
				pushPendingDecs(cur_oldroot, tinfo.decs_batch);
            }           
			oldroots_idx++;
        } 
        else {
            // In both lists
            roots_idx++, oldroots_idx++;
        }
    }

    tinfo.old_roots_count = 0;
}


static inline void handleTaggedObjectDecrement(void** slots, ArrayList<void*>& list) noexcept 
{
    __CoreGC::TypeInfoBase* tagged_typeinfo = (__CoreGC::TypeInfoBase*)*slots;
    switch(tagged_typeinfo->tag) {
        case __CoreGC::Tag::Ref: {
            pushPendingDecs(*(slots + 1), list); 
            break;
        }
        case __CoreGC::Tag::Tagged: {
            walkPointerMaskForDecrements(tagged_typeinfo, slots + 1, list); 
            break;
        }
        case __CoreGC::Tag::Value: {
            walkPointerMaskForDecrements(tagged_typeinfo, slots + 1, list);
            break;
        }
    }
}

static void walkPointerMaskForDecrements(__CoreGC::TypeInfoBase* typeinfo, void** slots, ArrayList<void*>& list) noexcept
{
    const char* ptr_mask = typeinfo->ptr_mask;
    if(ptr_mask == PTR_MASK_LEAF) {
        return ;
    }

    while(*ptr_mask != '\0') {
        switch(*ptr_mask) {
            case PTR_MASK_PTR: { 
                pushPendingDecs(*slots, list); 
                break;
            }
            case PTR_MASK_TAGGED: { 
                handleTaggedObjectDecrement(slots, list); 
                break; 
            }
            case PTR_MASK_NOP: { 
                break; 
            }
        }
 
        ptr_mask++;
        slots++;
    }
}

static inline void updateDecrementedPages(void* obj, ArrayList<PageInfo*>& pagelist) noexcept 
{
	std::lock_guard lk(g_gcmemlock);

	PageInfo* p = PageInfo::extractPageFromPointer(obj);
	if(!p->visited) {
		// If no owner, page must be alloc/evac so ignore as it will be rebuilt
		// next collection
        if(!p->owner) { 
    		return ;
        } 
	
        p->owner->remove(p);                                                                        
		p->visited = true;
		pagelist.push_back(p);
    }
}

static inline void decrementObject(void* obj) noexcept 
{
	MetaData* m = GC_GET_META_DATA_ADDR(obj);
    if(GC_REF_COUNT(m) > 0) {
        DEC_REF_COUNT(m);
    }
}

static inline void updateDecrementedObject(void* obj, ArrayList<void*>& list)
{
    MetaData* m = GC_GET_META_DATA_ADDR(obj); 
    __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(m);
    if(typeinfo->ptr_mask != PTR_MASK_LEAF && GC_REF_COUNT(m) == 0) {
        walkPointerMaskForDecrements(typeinfo, static_cast<void**>(obj), list);
        GC_RESET_ALLOC(m);
    }
}

// TODO call this inside processDecrements
void processDec(void* obj, ArrayList<void*>& decslist, ArrayList<PageInfo*>& pagelist) noexcept
{
	MetaData* m = GC_GET_META_DATA_ADDR(obj);	
    if(!GC_IS_ALLOCATED(m)) {
        return ;
    }

	decrementObject(obj);
    updateDecrementedObject(obj, decslist);
    updateDecrementedPages(obj, pagelist);
}

static inline void mergeDecList(BSQMemoryTheadLocalInfo& tinfo)
{
    while(!tinfo.decs_batch.isEmpty()) {
        void* obj = tinfo.decs_batch.pop_front();
        g_decs_prcsr.pending.push_back(obj);
    }
}

// If we did not finish decs in main thread pause decs thread, merge remaining work,
// then signal processing can continue
static void tryMergeDecList(BSQMemoryTheadLocalInfo& tinfo)
{
    if(g_decs_prcsr.processDecfp == nullptr) {
        g_decs_prcsr.processDecfp = processDec;
    }

    if(!tinfo.decs_batch.isEmpty()) {
        mergeDecList(tinfo);
    }
}

static void processDecrements(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
	std::lock_guard lk(g_gcrefctlock);   
	if(!tinfo.decd_pages.isInitialized()) {
		tinfo.decd_pages.initialize();
	}

    size_t deccount = 0;
    while(!tinfo.decs_batch.isEmpty() && (deccount < tinfo.max_decrement_count)) {
        void* obj = tinfo.decs_batch.pop_front();
	    MetaData* m = GC_GET_META_DATA_ADDR(obj);	
        if(!GC_IS_ALLOCATED(m)) {
            continue;
        }

        decrementObject(obj);
        updateDecrementedObject(obj, tinfo.decs_batch);
        updateDecrementedPages(obj, tinfo.decd_pages);

        deccount++;
    }

    //
    //TODO: we want to do a bit of PID controller here on the max decrement count to ensure that we eventually make it back to stable but keep pauses small
    //
}

static void* forward(void* ptr, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    PageInfo* p = PageInfo::extractPageFromPointer(ptr);
    GCAllocator* gcalloc = tinfo.getAllocatorForType(p);
    GC_INVARIANT_CHECK(gcalloc != nullptr);

    MetaData* m = GC_GET_META_DATA_ADDR(ptr); 
    void* nptr = gcalloc->allocateEvacuation(); 
	xmem_copy(ptr, nptr, p->typeinfo->slot_size);

    // Insert into forward table and update object ensuring future objects update
    RESET_METADATA_FOR_OBJECT(m, tinfo.forward_table_index);
    tinfo.forward_table[tinfo.forward_table_index++] = nptr;

    UPDATE_TOTAL_PROMOTIONS(+=, 1);

    return nptr;
}

static inline void updateRef(void** obj, BSQMemoryTheadLocalInfo& tinfo)
{
    void* ptr = *obj;

    // Root points to root case (may be a false root)
	MetaData* m = GC_GET_META_DATA_ADDR(ptr);
    if(GC_IS_ROOT(m) || !GC_IS_YOUNG(m)) {
        INC_REF_COUNT(m);
        return ;
    }

    int32_t fwd_index = GC_FWD_INDEX(m);
    if(fwd_index == NON_FORWARDED ) {
        *obj = forward(ptr, tinfo); 
    }
    else {
        *obj = tinfo.forward_table[fwd_index]; 
    }

	MetaData* nm = GC_GET_META_DATA_ADDR(*obj);	
    INC_REF_COUNT(nm);
}

static inline void handleTaggedObjectUpdate(void** slots, BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
    __CoreGC::TypeInfoBase* tagged_typeinfo = static_cast<__CoreGC::TypeInfoBase*>(*slots);
    switch(tagged_typeinfo->tag) {
        case __CoreGC::Tag::Ref: {
            updateRef(slots + 1, tinfo); 
            break;
        }
        case __CoreGC::Tag::Tagged: {
            updatePointers(slots + 1, tagged_typeinfo, tinfo); 
            break;
        }
        case __CoreGC::Tag::Value: {
            updatePointers(slots + 1, tagged_typeinfo, tinfo);
            break;
        }
    }
}

static void updatePointers(void** slots, __CoreGC::TypeInfoBase* typeinfo, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    const char* ptr_mask = typeinfo->ptr_mask;
    if(ptr_mask == PTR_MASK_LEAF) {
        return;
    }

    while(*ptr_mask != '\0') {
        switch(*ptr_mask) {
            case PTR_MASK_PTR: {
                updateRef(slots, tinfo); 
                break;
            }
            case PTR_MASK_TAGGED: { 
                handleTaggedObjectUpdate(slots, tinfo); 
                break;
            }
            case PTR_MASK_NOP: {
                break;
            }
        }

        ptr_mask++;
        slots++;
    }        
}

// Move non root young objects to evacuation page (as needed) then forward pointers and inc ref counts
static void processMarkedYoungObjects(BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
	std::lock_guard lk(g_gcrefctlock);
    while(!tinfo.pending_young.isEmpty()) {
        void* obj = tinfo.pending_young.pop_front(); //ensures non-roots visited first
		MetaData* m = GC_GET_META_DATA_ADDR(obj);       
 
        // A different object may forward this object, update with fwd table
        int32_t fwdidx = GC_FWD_INDEX(m);
		void* nobj = obj;
        if(fwdidx > NON_FORWARDED) {
            GC_INVARIANT_CHECK(fwdidx < gtl_info.forward_table_index);
            nobj = gtl_info.forward_table[fwdidx];
        }
		
		MetaData* nm = GC_GET_META_DATA_ADDR(nobj);
        __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(nm);
        updatePointers(static_cast<void**>(nobj), typeinfo, tinfo);

        if(GC_IS_ROOT(nm)) {
            GC_CLEAR_YOUNG_MARK(nm);
        }
    }
}

static inline bool pointsToObjectStart(void* addr) noexcept 
{
	// page->entrycount may be reset by another thread (setPageMetaData)
	std::lock_guard lk(g_alloclock);

    uintptr_t offset = reinterpret_cast<uintptr_t>(addr) & PAGE_MASK; 
    PageInfo* p = PageInfo::extractPageFromPointer(addr);
	if(offset < (sizeof(PageInfo) + METADATA_SEG_SIZE(p))) {
        return false;
    }

    uintptr_t start = GET_SLOT_START_FROM_OFFSET(offset, p);
    return start % p->realsize == 0;
}

// TODO might be nice to create an `Array<T, N>` class that provides qsort
// and binary search
// -- we can have this replace our raw arrays in tinfo
static bool find(void** arr, int32_t n, void* trgt, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    int32_t l = 0, r = tinfo.old_roots_count - 1;
    while(l <= r) {
        int32_t m = l + (r - l / 2);
        void* cur = tinfo.old_roots[m];
        if(cur < trgt) {
            l = m + 1;
        }
        else if(cur > trgt) {
            r = m - 1;
        }
        else {
            return true;
        }
    }

    return false;
}

// NOTE we could sort roots here then do two pointer walk on old roots, building
// up a set of dead objects to be merged onto decs list later
static void checkPotentialPtr(void* addr, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    if(!GlobalPageGCManager::g_gc_page_manager.pagetableQuery(addr) 
        || !pointsToObjectStart(addr)) {
            return ;
    }

	MetaData* m = PageInfo::getObjectMetadataAligned(addr);
	if(GC_IS_MARKED(m)) {
		return ;
	}
	GC_MARK_AS_MARKED(m);

	tinfo.roots[tinfo.roots_count++] = addr;
	if(!find(tinfo.old_roots, tinfo.old_roots_count, addr, tinfo)) {		
		GC_MARK_AS_ROOT(m);

		// another thread may reference this root, so needs to be young 
		// to be eligible for processing
		if(GC_SHOULD_PROCESS_AS_YOUNG(m)) {
			tinfo.pending_roots.push_back(addr);
		}
	}
}

static void walkStack(BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
	std::lock_guard lk(g_gcrefctlock); 
	
	if(GlobalDataStorage::g_global_data.needs_scanning) {
        void** curr = GlobalDataStorage::g_global_data.native_global_storage;
        while(curr < GlobalDataStorage::g_global_data.native_global_storage_end) {
            checkPotentialPtr(*curr, tinfo);
            curr++;
        }
#ifndef BSQ_GC_TESTING
        GlobalDataStorage::g_global_data.needs_scanning = false;
#endif
    }

#ifdef BSQ_GC_TESTING
	if(g_thd_testing) {
		for(unsigned i = 0; i < NUM_THREAD_TESTING_ROOTS; i++) {
			void* cur = tinfo.thd_testing_data[i]; 
			checkPotentialPtr(cur, tinfo);		
		}
	}
#endif
    if(g_disable_stack_refs) {
        goto cleanup;
    }
    
    tinfo.loadNativeRootSet();

    while(!tinfo.native_stack_contents.isEmpty()) {
        checkPotentialPtr(tinfo.native_stack_contents.pop_front(), tinfo);
    }

    checkPotentialPtr(tinfo.native_register_contents.rax, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.rbx, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.rcx, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.rdx, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.rsi, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.rdi, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.r8, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.r9, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.r10, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.r11, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.r12, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.r13, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.r14, tinfo);
    checkPotentialPtr(tinfo.native_register_contents.r15, tinfo);

    tinfo.unloadNativeRootSet();

[[maybe_unused]] cleanup:
	// Mark bit is used to ensure we dont inc thd count multiple times 
	// (say a root ref is in both registers and stack), so clear before
	// marking (maybe a cleaner way to handle this?)
	for(int32_t i = 0; i < tinfo.roots_count; i++) {
		MetaData* m = GC_GET_META_DATA_ADDR(tinfo.roots[i]);
		GC_CLEAR_MARKED_MARK(m);
	}
}

static void markRef(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept
{
    MetaData* m = GC_GET_META_DATA_ADDR(*slots);
    GC_CHECK_BOOL_BYTES(m);
    
	if(GC_SHOULD_VISIT(m)) { 
		GC_MARK_AS_MARKED(m);
		tinfo.visit_stack.push_back({*slots, MARK_STACK_NODE_COLOR_GREY});
    }
}

static void handleMarkingTaggedObject(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept 
{ 
    __CoreGC::TypeInfoBase* tagged_typeinfo = static_cast<__CoreGC::TypeInfoBase*>(*slots);
    switch(tagged_typeinfo->tag) {
        case __CoreGC::Tag::Ref: {
            markRef(tinfo, slots + 1); 
            break;
        }
        case __CoreGC::Tag::Tagged: {
            walkPointerMaskForMarking(tinfo, tagged_typeinfo, slots + 1); 
            break;
        }
        case __CoreGC::Tag::Value: { 
            // Need to scan for inline objects!
            walkPointerMaskForMarking(tinfo, tagged_typeinfo, slots + 1);
            break;
        }
    }
}

static void walkPointerMaskForMarking(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept 
{
    const char* ptr_mask = typeinfo->ptr_mask;
    if(ptr_mask == PTR_MASK_LEAF) {
        return ;
    } 

    while(*ptr_mask != '\0') {
        switch(*ptr_mask) {
            case PTR_MASK_PTR: {
                markRef(tinfo, slots); 
                break;
            }
            case PTR_MASK_TAGGED: {
                handleMarkingTaggedObject(tinfo, slots); 
                break;
            }
            case PTR_MASK_NOP: {
                break;
            }
        }

        ptr_mask++;
        slots++;
    }
}

static void walkSingleRoot(void* root, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    while(!tinfo.visit_stack.isEmpty()) {
        MarkStackEntry entry = tinfo.visit_stack.pop_back();
		MetaData* m = GC_GET_META_DATA_ADDR(entry.obj);
        __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(m);

        // Can we process further?
        if((typeinfo->ptr_mask == PTR_MASK_LEAF) || (entry.color == MARK_STACK_NODE_COLOR_BLACK)) {
            tinfo.pending_young.push_back(entry.obj);
            continue;
        }
        
        tinfo.visit_stack.push_back({entry.obj, MARK_STACK_NODE_COLOR_BLACK});
        walkPointerMaskForMarking(tinfo, typeinfo, (void**)entry.obj);
     }
}

static void markingWalk(BSQMemoryTheadLocalInfo& tinfo) noexcept
{   
    gtl_info.pending_roots.initialize();
    gtl_info.visit_stack.initialize();

    walkStack(tinfo);

    // Process the walk stack
    while(!tinfo.pending_roots.isEmpty()) {
        void* obj = tinfo.pending_roots.pop_front();
		MetaData* m = GC_GET_META_DATA_ADDR(obj);
		if(GC_SHOULD_VISIT(m)) {
			GC_MARK_AS_MARKED(m);
			tinfo.visit_stack.push_back({obj, MARK_STACK_NODE_COLOR_GREY});
			walkSingleRoot(obj, tinfo);
		}
    }

    gtl_info.visit_stack.clear();
    gtl_info.pending_roots.clear();
}

static void processAllocatorsPages(BSQMemoryTheadLocalInfo& tinfo)
{
    UPDATE_TOTAL_LIVE_BYTES(=, 0);
    for(size_t i = 0; i < BSQ_MAX_ALLOC_SLOTS; i++) {
        GCAllocator* alloc = tinfo.g_gcallocs[i];
        if(alloc != nullptr) {
            alloc->processCollectorPages(&tinfo);
        }
    }
}
	
static inline void computeMaxDecrementCount(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
	tinfo.max_decrement_count = BSQ_INITIAL_MAX_DECREMENT_COUNT - (tinfo.bytes_freed / BSQ_MEM_ALIGNMENT);
	tinfo.bytes_freed = 0;
}

static void updateRoots(BSQMemoryTheadLocalInfo& tinfo)
{
    xmem_zerofill(tinfo.old_roots, tinfo.old_roots_count);
    tinfo.old_roots_count = 0;

    for(int32_t i = 0; i < gtl_info.roots_count; i++) {
		void* obj = tinfo.roots[i];
		MetaData* m = GC_GET_META_DATA_ADDR(obj);
        GC_CLEAR_YOUNG_MARK(m);
		GC_CLEAR_MARKED_MARK(m);

        tinfo.old_roots[tinfo.old_roots_count++] = obj;
    }

    xmem_zerofill(tinfo.roots, tinfo.roots_count);
    tinfo.roots_count = 0;
}

// NOTE we need to be weary of the possibility of pages being rebuilt inside of 
// processAllocatorsPages but also need rebuilding after decs
void collect() noexcept
{
    COLLECTION_STATS_START();

	// TODO we should explore possibilities for not needing to pause for the
	// full collection!
    g_decs_prcsr.pause();	
	g_decs_prcsr.mergeDecdPages(gtl_info.decd_pages);

    gtl_info.pending_young.initialize();

    NURSERY_STATS_START();

	// Mark, compact, reprocess pages
    markingWalk(gtl_info);
    processMarkedYoungObjects(gtl_info);
    processAllocatorsPages(gtl_info);
    
	NURSERY_STATS_END(nursery_times);

    gtl_info.pending_young.clear();

    xmem_zerofill(gtl_info.forward_table, gtl_info.forward_table_index);
    gtl_info.forward_table_index = FWD_TABLE_START;

    gtl_info.decs_batch.initialize();

	computeMaxDecrementCount(gtl_info);

	// Find dead roots, walk object graph from dead roots updating necessary rcs
	// rebuild pages who saw decs (TODO do this lazily), and merge remainder of decs
	// (TODO use a single shared list (?))    	
  	RC_STATS_START();
 
    computeDeadRootsForDecrement(gtl_info);
    processDecrements(gtl_info);	
	tryMergeDecList(gtl_info);

	RC_STATS_END(rc_times);

    gtl_info.decs_batch.clear();

    // Cleanup for next collection
    updateRoots(gtl_info);

    COLLECTION_STATS_END(collection_times);

    UPDATE_MEMSTATS_TOTALS(gtl_info);

    g_decs_prcsr.resume();
}
