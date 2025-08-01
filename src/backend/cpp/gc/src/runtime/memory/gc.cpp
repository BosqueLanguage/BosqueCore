#include "allocator.h"
#include "gc.h"
#include "../support/qsort.h"
#include "threadinfo.h"

#ifdef MEM_STATS
#include <chrono>
#endif

// Used to determine if a pointer points into the data segment of an object
#define POINTS_TO_DATA_SEG(P) P >= (void*)PAGE_FIND_OBJ_BASE(P) && P < (void*)((char*)PAGE_FIND_OBJ_BASE(P) + PAGE_MASK_EXTRACT_PINFO(P)->entrysize)

#define INC_REF_COUNT(O) (++GC_REF_COUNT(O))
#define DEC_REF_COUNT(O) (--GC_REF_COUNT(O))

void walkPointerMaskForDecrements(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept;
void updatePointers(void** slots, const BSQMemoryTheadLocalInfo& tinfo) noexcept;
void walkPointerMaskForMarking(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept; 

void reprocessPageInfo(PageInfo* page, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    // This should not be called on pages that are (1) active allocators or evacuators or (2) pending collection pages
    GCAllocator* gcalloc = tinfo.getAllocatorForPageSize(page);
    if(gcalloc->checkNonAllocOrGCPage(page)) {
        gcalloc->deleteOldPage(page);
        gcalloc->processPage(page);
    }
}

void computeDeadRootsForDecrement(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    // First we need to sort the roots we find
    qsort(tinfo.roots, 0, tinfo.roots_count - 1, tinfo.roots_count);

    size_t roots_idx = 0;
    size_t oldroots_idx = 0;

    while(oldroots_idx < tinfo.old_roots_count) {
        void* cur_oldroot = tinfo.old_roots[oldroots_idx];
        
        if(roots_idx >= tinfo.roots_count) {
            // Was dropped from roots
            tinfo.pending_decs.push_back(cur_oldroot);
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
            tinfo.pending_decs.push_back(cur_oldroot);
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

bool pageNeedsMoved(float old_util, float new_util)
{
    // Case where page hasnt been processed before
    if (old_util > 1.1f) {
        return false;
    }

    // Handle empty page case
    if (new_util < 0.01f && old_util > 0.01f) {
        return true;
    }

    const bool was_low_util = IS_LOW_UTIL(old_util);
    const bool now_low_util = IS_LOW_UTIL(new_util);
    if (was_low_util != now_low_util) {
        return true;
    }

    const bool was_high_util = IS_HIGH_UTIL(old_util);
    const bool now_high_util = IS_HIGH_UTIL(new_util);
    if (was_high_util != now_high_util) {
        return true;
    }

    const bool was_full = IS_FULL(old_util);
    const bool now_full = IS_FULL(new_util);
    if (was_full != now_full) {
        return true;
    }

    if (now_low_util) {
        int old_bucket = -1; 
        int new_bucket = -1;
        GET_BUCKET_INDEX(old_util, NUM_LOW_UTIL_BUCKETS, old_bucket, 0);
        GET_BUCKET_INDEX(new_util, NUM_LOW_UTIL_BUCKETS, new_bucket, 0);
        return old_bucket != new_bucket;
    } 
    else if (now_high_util){
        int old_bucket = -1; 
        int new_bucket = -1;
        GET_BUCKET_INDEX(old_util, NUM_HIGH_UTIL_BUCKETS, old_bucket, 1);
        GET_BUCKET_INDEX(new_util, NUM_HIGH_UTIL_BUCKETS, new_bucket, 1);
        return old_bucket != new_bucket;
    }
    else {
        return false;
    }
}

inline void pushPendingDecs(BSQMemoryTheadLocalInfo& tinfo, void** obj)
{
    PageInfo::extractPageFromPointer(*obj)->pending_decs_count++;
    tinfo.pending_decs.push_back(*obj);
}

inline void handleRefDecrement(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept 
{
    void* obj = *slots;
    uint32_t refcount = DEC_REF_COUNT(obj);
    if(refcount != 0 || !GC_IS_ROOT(obj)) {
        return ;
    }

    pushPendingDecs(tinfo, slots);
}

inline void handleTaggedObjectDecrement(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept 
{
    __CoreGC::TypeInfoBase* tagged_typeinfo = (__CoreGC::TypeInfoBase*)*slots;
    switch(tagged_typeinfo->tag) {
        case __CoreGC::Tag::Ref: {
            handleRefDecrement(tinfo, slots + 1); 
            break;
        }
        case __CoreGC::Tag::Tagged: {
            walkPointerMaskForDecrements(tinfo, tagged_typeinfo, slots + 1); 
            break;
        }
        case __CoreGC::Tag::Value: {
            return ;
        }
    }
}

void walkPointerMaskForDecrements(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept
{
    const char* ptr_mask = typeinfo->ptr_mask;
    if(ptr_mask == PTR_MASK_LEAF) {
        return ;
    }

    while(*ptr_mask != '\0') {
        switch(*ptr_mask) {
            case PTR_MASK_PTR: { 
                handleRefDecrement(tinfo, slots); 
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

void processDecrements(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    GC_REFCT_LOCK_ACQUIRE();
    MEM_STATS_START();

    size_t deccount = 0;
    while(!tinfo.pending_decs.isEmpty() && (deccount < tinfo.max_decrement_count)) {
        void* obj = tinfo.pending_decs.pop_front();
        deccount++;

        // Skip if the object is already freed
        if (!GC_IS_ALLOCATED(obj)) {
            continue;
        }

        // Decrement ref counts of objects this object points to
        __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(obj);

        if(typeinfo->ptr_mask != PTR_MASK_LEAF) {
            walkPointerMaskForDecrements(tinfo, typeinfo, (void**)obj);
        }

        // Put object onto its pages freelist by masking to the page itself then pushing to front of list 
        PageInfo* objects_page = PageInfo::extractPageFromPointer(obj);
        FreeListEntry* entry = (FreeListEntry*)((uint8_t*)obj - sizeof(MetaData));
        entry->next = objects_page->freelist;
        objects_page->freelist = entry;

        // Need to make sure pending decs count is not 0 already, this prevents us from
        // decrementing dec count for the root object and wrapping to max uint16
        if(objects_page->pending_decs_count != 0) {
            objects_page->pending_decs_count--;
        }

        // Mark the object as unallocated
        GC_IS_ALLOCATED(obj) = false;

        objects_page->freecount++;
        tinfo.decremented_pages[tinfo.decremented_pages_index++] = objects_page;
    }

    for(int i = 0; i < tinfo.decremented_pages_index; i++) {        
        // We only want to move pages without pending decs
        // We can think of these pages as stable
        PageInfo* p = tinfo.decremented_pages[i];
        if(p->pending_decs_count > 0) {
            continue;
        }

        if(pageNeedsMoved(p->approx_utilization, CALC_APPROX_UTILIZATION(p))) {
            reprocessPageInfo(p, tinfo);
        }
    }
    tinfo.decremented_pages_index = 0;

    MEM_STATS_END(decrement_times, decrement_times_index);
    GC_REFCT_LOCK_RELEASE();

    //
    //TODO: we want to do a bit of PID controller here on the max decrement count to ensure that we eventually make it back to stable but keep pauses small
    //
}

inline void updateRef(void** obj, const BSQMemoryTheadLocalInfo& tinfo)
{
    uint32_t fwd_index = GC_FWD_INDEX(*obj);
    if(fwd_index != MAX_FWD_INDEX) {
        *obj = tinfo.forward_table[fwd_index]; 
    }
    
    // Prevent possible ref count increase of a non-forwarded object
    if(*obj == nullptr) {
        return ;
    }

    INC_REF_COUNT(*obj);
}

inline void handleTaggedObjectUpdate(void** slots, const BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
    __CoreGC::TypeInfoBase* tagged_typeinfo = (__CoreGC::TypeInfoBase*)*slots;
    switch(tagged_typeinfo->tag) {
        case __CoreGC::Tag::Ref: {
            updateRef(slots + 1, tinfo); 
            break;
        }
        case __CoreGC::Tag::Tagged: {
            updatePointers(slots + 1, tinfo); 
            break;
        }
        case __CoreGC::Tag::Value: {
            return ;
        }
    }
}

// Update pointers using forward table
void updatePointers(void** slots, const BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    __CoreGC::TypeInfoBase* type_info = GC_TYPE(slots);
    const char* ptr_mask = type_info->ptr_mask;
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
void processMarkedYoungObjects(BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
    GC_REFCT_LOCK_ACQUIRE();
    MEM_STATS_START();

    while(!tinfo.pending_young.isEmpty()) {
        void* obj = tinfo.pending_young.pop_front();
        __CoreGC::TypeInfoBase* type_info = GC_TYPE(obj);
        GC_INVARIANT_CHECK(GC_IS_YOUNG(obj) && GC_IS_MARKED(obj));

        if(GC_IS_ROOT(obj)) {
            updatePointers((void**)obj, tinfo);
            GC_CLEAR_YOUNG_MARK(GC_GET_META_DATA_ADDR(obj));
            continue;
        }
        
        // If we are not a root we want to evacuate
        GCAllocator* gcalloc = tinfo.getAllocatorForPageSize(PageInfo::extractPageFromPointer(obj));
        GC_INVARIANT_CHECK(gcalloc != nullptr);
    
        void* newobj = gcalloc->allocateEvacuation(type_info);
        xmem_copy(obj, newobj, type_info->slot_size);
        updatePointers((void**)newobj, tinfo);

        RESET_METADATA_FOR_OBJECT(GC_GET_META_DATA_ADDR(obj), (uint32_t)tinfo.forward_table_index);
        tinfo.forward_table[tinfo.forward_table_index++] = newobj;
    }

    MEM_STATS_END(evacuation_times, evacuation_times_index);
    GC_REFCT_LOCK_RELEASE();
}

void checkPotentialPtr(void* addr, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    // Make sure our page is in pagetable, our address is not a page itself,
    // or a pointer into the page's metadata
    uintptr_t page_offset = (uintptr_t)addr & 0xFFF;

    if(!GlobalPageGCManager::g_gc_page_manager.pagetable_query(addr)
        || page_offset < sizeof(PageInfo)) {
            return ;
    }

    MetaData* meta = PageInfo::getObjectMetadataAligned(addr);
    void* obj = (void*)((uint8_t*)meta + sizeof(MetaData));
    
    if(!GC_SHOULD_PROCESS_AS_ROOT(meta)) {
        return ;
    }

    //Need to verify our object is allocated and not already marked
    GC_MARK_AS_ROOT(meta);

    tinfo.roots[tinfo.roots_count++] = obj;
    if(GC_SHOULD_PROCESS_AS_YOUNG(meta)) {
        tinfo.pending_roots.push_back(obj);
    }
 }

void walkStack(BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
    // Process global data (TODO -- later have flag to disable this after it is fixed as immortal)
    if(GlobalDataStorage::g_global_data.native_global_storage != nullptr) {
        void** curr = GlobalDataStorage::g_global_data.native_global_storage;
        while(curr < GlobalDataStorage::g_global_data.native_global_storage_end) {
            checkPotentialPtr(*curr, tinfo);
            curr++;
        }
    }

#ifdef BSQ_GC_CHECK_ENABLED
    if(tinfo.disable_stack_refs_for_tests) {
        return;
    }
#endif
    
    tinfo.loadNativeRootSet();

    for(size_t i = 0; i < tinfo.native_stack_count; i++) {
        checkPotentialPtr(tinfo.native_stack_contents[i], tinfo);
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

void markRef(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept
{
    MetaData* meta = GC_GET_META_DATA_ADDR(*slots);
    if(meta == nullptr) {
        assert(false);
    }

    if(!GC_SHOULD_VISIT(meta)) {
        return ;
    }
    
    GC_MARK_AS_MARKED(meta);
    tinfo.visit_stack.push_back({*slots, MARK_STACK_NODE_COLOR_GREY});
}

void handleMarkingTaggedObject(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept 
{
    __CoreGC::TypeInfoBase* tagged_typeinfo = (__CoreGC::TypeInfoBase*)*slots;
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
            return ;
        }
    }
}

void walkPointerMaskForMarking(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept 
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

void walkSingleRoot(void* root, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    while(!tinfo.visit_stack.isEmpty()) {
        MarkStackEntry entry = tinfo.visit_stack.pop_back();
        __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(entry.obj);

        if((typeinfo->ptr_mask == PTR_MASK_LEAF) || (entry.color == MARK_STACK_NODE_COLOR_BLACK)) {
            // No children so do by definition
            tinfo.pending_young.push_back(entry.obj);
            continue;
        }
        
        tinfo.visit_stack.push_back({entry.obj, MARK_STACK_NODE_COLOR_BLACK});
        walkPointerMaskForMarking(tinfo, typeinfo, (void**)entry.obj);
     }
}

void markingWalk(BSQMemoryTheadLocalInfo& tinfo) noexcept
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

    MEM_STATS_END(marking_times, marking_times_index);
}

void collect() noexcept
{   
    MEM_STATS_START();

    static bool should_reset_pending_decs = true;
    gtl_info.pending_young.initialize();
    markingWalk(gtl_info);
    processMarkedYoungObjects(gtl_info);
    gtl_info.pending_young.clear();

    xmem_zerofill(gtl_info.forward_table, gtl_info.forward_table_index);
    gtl_info.forward_table_index = 0;

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

    UPDATE_TOTAL_LIVE_BYTES(gtl_info, ++);
    for(size_t i = 0; i < BSQ_MAX_ALLOC_SLOTS; i++) {
        GCAllocator* alloc = gtl_info.g_gcallocs[i];
        if(alloc != nullptr) {
            alloc->processCollectorPages();
            alloc->updateMemStats();
        }
    }

    xmem_zerofill(gtl_info.old_roots, gtl_info.old_roots_count);
    gtl_info.old_roots_count = 0;

    for(size_t i = 0; i < gtl_info.roots_count; i++) {
        GC_CLEAR_ROOT_MARK(GC_GET_META_DATA_ADDR(gtl_info.roots[i]));

        gtl_info.old_roots[gtl_info.old_roots_count++] = gtl_info.roots[i];
    }

    xmem_zerofill(gtl_info.roots, gtl_info.roots_count);
    gtl_info.roots_count = 0;
    gtl_info.newly_filled_pages_count = 0;

    MEM_STATS_END(collection_times, collection_times_index);
}