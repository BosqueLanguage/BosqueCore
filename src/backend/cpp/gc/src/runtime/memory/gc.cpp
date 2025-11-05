#include "allocator.h"
#include "gc.h"
#include "../support/qsort.h"
#include "threadinfo.h"

#ifdef MEM_STATS
#include <chrono>
#endif

// Used to determine if a pointer points into the data segment of an object
#define POINTS_TO_DATA_SEG(P) P >= (void*)PAGE_FIND_OBJ_BASE(P) && P < (void*)((char*)PAGE_FIND_OBJ_BASE(P) + PAGE_MASK_EXTRACT_PINFO(P)->entrysize)

#ifdef ALLOC_DEBUG_CANARY
#define GET_SLOT_START_FROM_OFFSET(O) (O - sizeof(PageInfo) - sizeof(MetaData) - ALLOC_DEBUG_CANARY_SIZE) 
#else 
#define GET_SLOT_START_FROM_OFFSET(O) (O - sizeof(PageInfo) - sizeof(MetaData)) 
#endif

static void walkPointerMaskForDecrements(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept;
static void updatePointers(void** slots, __CoreGC::TypeInfoBase* typeinfo, BSQMemoryTheadLocalInfo& tinfo) noexcept;
static void walkPointerMaskForMarking(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept; 

static void reprocessPageInfo(PageInfo* page, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    // This should not be called on pages that are (1) active allocators or evacuators or (2) pending collection pages
    GCAllocator* gcalloc = tinfo.getAllocatorForPageSize(page);
    PageInfo* npage = gcalloc->tryRemoveFromFilledPages(page);
    if(npage != nullptr) {
        npage->rebuild();
        gcalloc->processPage(npage);
    }
}

static inline void pushPendingDecs(BSQMemoryTheadLocalInfo& tinfo, void* obj)
{
    // Dead root points to root case, keep the root pointed to alive
    if(GC_IS_ROOT(obj)) [[unlikely]] {
        return ;
    }

    PageInfo::extractPageFromPointer(obj)->pending_decs_count++;
    tinfo.pending_decs.push_back(obj);
}

static void computeDeadRootsForDecrement(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    // First we need to sort the roots we find
    qsort(tinfo.roots, 0, tinfo.roots_count - 1, tinfo.roots_count);

    int32_t roots_idx = 0;
    int32_t oldroots_idx = 0;

    while(oldroots_idx < tinfo.old_roots_count) {
        void* cur_oldroot = tinfo.old_roots[oldroots_idx];
        
        if(roots_idx >= tinfo.roots_count) {
            // Was dropped from roots
            if(GC_REF_COUNT(cur_oldroot) == 0) {
                pushPendingDecs(tinfo, cur_oldroot);
            }
            oldroots_idx++;
            continue;
        }
        
        void* cur_root = tinfo.roots[roots_idx];
        if(cur_root < cur_oldroot) {
            // New root in current
            roots_idx++;
        } 
        else if(cur_oldroot < cur_root) {
            // Was dropped from roots
            if(GC_REF_COUNT(cur_oldroot) == 0) {
                pushPendingDecs(tinfo, cur_oldroot);
            }
            oldroots_idx++;
        } 
        else {
            // In both lists
            roots_idx++;
            oldroots_idx++;
        }
    }

    tinfo.old_roots_count = 0;
}

static inline void handleTaggedObjectDecrement(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept 
{
    __CoreGC::TypeInfoBase* tagged_typeinfo = (__CoreGC::TypeInfoBase*)*slots;
    switch(tagged_typeinfo->tag) {
        case __CoreGC::Tag::Ref: {
            pushPendingDecs(tinfo, *(slots + 1)); 
            break;
        }
        case __CoreGC::Tag::Tagged: {
            walkPointerMaskForDecrements(tinfo, tagged_typeinfo, slots + 1); 
            break;
        }
        case __CoreGC::Tag::Value: {
            walkPointerMaskForDecrements(tinfo, tagged_typeinfo, slots + 1);
            break;
        }
    }
}

static void walkPointerMaskForDecrements(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept
{
    const char* ptr_mask = typeinfo->ptr_mask;
    if(ptr_mask == PTR_MASK_LEAF) {
        return ;
    }

    while(*ptr_mask != '\0') {
        switch(*ptr_mask) {
            case PTR_MASK_PTR: { 
                pushPendingDecs(tinfo, *slots); 
                break;
            }
            case PTR_MASK_TAGGED: { 
                handleTaggedObjectDecrement(tinfo, slots); 
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

static inline void updateDecrementedPages(PageInfo* p, BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
    if(p->seen == false) {
        p->seen = true;
        tinfo.decremented_pages[tinfo.decremented_pages_index++] = p;
    }
}

static inline void decrementObject(void* obj, BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
    if(GC_REF_COUNT(obj) > 0) {
        DEC_REF_COUNT(obj);
    }
}

static inline void updateDecrementedObject(void* obj, BSQMemoryTheadLocalInfo& tinfo)
{
    __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(obj);
    
    if(typeinfo->ptr_mask != PTR_MASK_LEAF && GC_REF_COUNT(obj) == 0) {
        walkPointerMaskForDecrements(tinfo, typeinfo, static_cast<void**>(obj));

        MetaData* m = GC_GET_META_DATA_ADDR(obj);
        GC_RESET_ALLOC(m);
    }
}

static inline void tryReprocessDecrementedPages(BSQMemoryTheadLocalInfo& tinfo)
{
    for(uint32_t i = 0; i < tinfo.decremented_pages_index; i++) {        
        reprocessPageInfo(tinfo.decremented_pages[i], tinfo);
    }
    tinfo.decremented_pages_index = 0;
}

static void processDecrements(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    GC_REFCT_LOCK_ACQUIRE();
    MEM_STATS_START();

    size_t deccount = 0;
    while(!tinfo.pending_decs.isEmpty() && (deccount < tinfo.max_decrement_count)) {
        void* obj = tinfo.pending_decs.pop_front();

        if(!GC_IS_ALLOCATED(obj)) {
            continue;
        }

        decrementObject(obj, tinfo);
        updateDecrementedObject(obj, tinfo);

        PageInfo* p = PageInfo::extractPageFromPointer(obj);
        p->decrementPendingDecs();
        updateDecrementedPages(p, tinfo);

        deccount++;
    }
    tryReprocessDecrementedPages(tinfo);

    MEM_STATS_END(decrement_times);
    GC_REFCT_LOCK_RELEASE();

    //
    //TODO: we want to do a bit of PID controller here on the max decrement count to ensure that we eventually make it back to stable but keep pauses small
    //
}

static void* forward(void* ptr, BSQMemoryTheadLocalInfo& tinfo)
{
    PageInfo* p = PageInfo::extractPageFromPointer(ptr);
    GCAllocator* gcalloc = tinfo.getAllocatorForPageSize(p);
    GC_INVARIANT_CHECK(gcalloc != nullptr);

    __CoreGC::TypeInfoBase* type_info = GC_TYPE(ptr);
    void* nptr = gcalloc->allocateEvacuation(type_info);
    xmem_copy(ptr, nptr, type_info->slot_size);

    // Insert into forward table and update object ensuring future objects update
    MetaData* m = GC_GET_META_DATA_ADDR(ptr); 
    RESET_METADATA_FOR_OBJECT(m, tinfo.forward_table_index);
    tinfo.forward_table[tinfo.forward_table_index] = nptr;
    tinfo.forward_table_index++;

    UPDATE_TOTAL_PROMOTIONS(gtl_info, +=, 1);

    return nptr;
}

static inline void updateRef(void** obj, BSQMemoryTheadLocalInfo& tinfo)
{
    void* ptr = *obj;

    // Root points to root case (may be a false root)
    if(GC_IS_ROOT(ptr) || !GC_IS_YOUNG(ptr)) {
        INC_REF_COUNT(ptr);
        return ;
    }

    int32_t fwd_index = GC_FWD_INDEX(ptr);
    if(fwd_index == NON_FORWARDED ) {
        *obj = forward(ptr, tinfo); 
    }
    else {
        *obj = tinfo.forward_table[fwd_index]; 
    }

    INC_REF_COUNT(*obj);
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
            // Need to scan for inline tagged types!
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
    GC_REFCT_LOCK_ACQUIRE();
    MEM_STATS_START();

    while(!tinfo.pending_young.isEmpty()) {
        void* obj = tinfo.pending_young.pop_front(); //ensures non-roots visited first
        
        // Skip already forwarded objects (those that may have multiple refers)
        if(GC_FWD_INDEX(obj) > NON_FORWARDED) {
            continue;
        }

        __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(obj);
        updatePointers((void**)obj, typeinfo, tinfo);

        if(GC_IS_ROOT(obj)) {
            MetaData* m = GC_GET_META_DATA_ADDR(obj);
            GC_CLEAR_YOUNG_MARK(m);
        }
    }

    MEM_STATS_END(evacuation_times);
    GC_REFCT_LOCK_RELEASE();
}

static inline bool pointsToObjectStart(void* addr) noexcept 
{
    uintptr_t offset = reinterpret_cast<uintptr_t>(addr) & PAGE_MASK;
    if(offset < sizeof(PageInfo)) {
        return false;
    }

    PageInfo* p = PageInfo::extractPageFromPointer(addr);
    uintptr_t start = GET_SLOT_START_FROM_OFFSET(offset);

    return start % p->realsize == 0;
}

static void checkPotentialPtr(void* addr, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    if(!GlobalPageGCManager::g_gc_page_manager.pagetable_query(addr) 
        || !pointsToObjectStart(addr)) {
            return ;
    }

    MetaData* meta = PageInfo::getObjectMetadataAligned(addr);
    void* obj = (void*)((uint8_t*)meta + sizeof(MetaData));

    if(GC_SHOULD_PROCESS_AS_ROOT(meta)) { 
        GC_MARK_AS_ROOT(meta);

        tinfo.roots[tinfo.roots_count++] = obj;
        if(GC_SHOULD_PROCESS_AS_YOUNG(meta)) {
            tinfo.pending_roots.push_back(obj);
        } 
    }
}

static void walkStack(BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
    if(GlobalDataStorage::g_global_data.needs_scanning) {
        void** curr = GlobalDataStorage::g_global_data.native_global_storage;
        while(curr < GlobalDataStorage::g_global_data.native_global_storage_end) {
            checkPotentialPtr(*curr, tinfo);
            curr++;
        }
        GlobalDataStorage::g_global_data.needs_scanning = false;
    }

#ifdef BSQ_GC_CHECK_ENABLED
    if(tinfo.enable_global_rescan) {
        GlobalDataStorage::g_global_data.needs_scanning = true;
    }

    if(tinfo.disable_stack_refs_for_tests) {
        return;
    }
#endif
    
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
}

static void markRef(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept
{
    MetaData* meta = GC_GET_META_DATA_ADDR(*slots);
    GC_CHECK_BOOL_BYTES(meta);
    
    if(GC_SHOULD_VISIT(meta)) { 
        GC_MARK_AS_MARKED(meta);
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
            // Need to scan for inline tagged objects!
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
        __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(entry.obj);

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
    MEM_STATS_START();
    
    gtl_info.pending_roots.initialize();
    gtl_info.visit_stack.initialize();

    walkStack(tinfo);

    // Process the walk stack
    while(!tinfo.pending_roots.isEmpty()) {
        void* obj = tinfo.pending_roots.pop_front();
        MetaData* meta = GC_GET_META_DATA_ADDR(obj);
        if(GC_SHOULD_VISIT(meta)) {
            GC_MARK_AS_MARKED(meta);

            tinfo.visit_stack.push_back({obj, MARK_STACK_NODE_COLOR_GREY});
            walkSingleRoot(obj, tinfo);
        }
    }

    gtl_info.visit_stack.clear();
    gtl_info.pending_roots.clear();

    MEM_STATS_END(marking_times);
}

void collect() noexcept
{
    UPDATE_TOTAL_COLLECTIONS(gtl_info, +=, 1);
    MEM_STATS_START();

    static bool should_reset_pending_decs = true;
    gtl_info.pending_young.initialize();
    markingWalk(gtl_info);
    processMarkedYoungObjects(gtl_info);
    gtl_info.pending_young.clear();

    xmem_zerofill(gtl_info.forward_table, gtl_info.forward_table_index);
    gtl_info.forward_table_index = FWD_TABLE_START;

    if(should_reset_pending_decs) {
        gtl_info.pending_decs.initialize();
        should_reset_pending_decs = false;
    }
    computeDeadRootsForDecrement(gtl_info);
    processDecrements(gtl_info);

    if(gtl_info.pending_decs.isEmpty()) {
        gtl_info.pending_decs.clear();
        should_reset_pending_decs = true;
    }

    UPDATE_TOTAL_LIVE_BYTES(gtl_info, =, 0);
    for(size_t i = 0; i < BSQ_MAX_ALLOC_SLOTS; i++) {
        GCAllocator* alloc = gtl_info.g_gcallocs[i];
        if(alloc != nullptr) {
            alloc->processCollectorPages();
        }
    }

    xmem_zerofill(gtl_info.old_roots, gtl_info.old_roots_count);
    gtl_info.old_roots_count = 0;

    for(int32_t i = 0; i < gtl_info.roots_count; i++) {
        GC_CLEAR_ROOT_MARK(GC_GET_META_DATA_ADDR(gtl_info.roots[i]));
        GC_CLEAR_YOUNG_MARK(GC_GET_META_DATA_ADDR(gtl_info.roots[i]));

        gtl_info.old_roots[gtl_info.old_roots_count++] = gtl_info.roots[i];
    }

    xmem_zerofill(gtl_info.roots, gtl_info.roots_count);
    gtl_info.roots_count = 0;
    gtl_info.newly_filled_pages_count = 0;

    MEM_STATS_END(collection_times);
    UPDATE_MEMSTATS();
}