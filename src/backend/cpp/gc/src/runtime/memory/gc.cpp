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

static void walkPointerMaskForDecrements(BSQMemoryTheadLocalInfo& tinfo, __CoreGC::TypeInfoBase* typeinfo, void** slots) noexcept;
static void updatePointers(void** slots, BSQMemoryTheadLocalInfo& tinfo) noexcept;
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
    PageInfo::extractPageFromPointer(obj)->pending_decs_count++;
    tinfo.pending_decs.push_back(obj);
}

static void computeDeadRootsForDecrement(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    // First we need to sort the roots we find
    qsort(tinfo.roots, 0, tinfo.roots_count - 1, tinfo.roots_count);

    size_t roots_idx = 0;
    size_t oldroots_idx = 0;

    while(oldroots_idx < tinfo.old_roots_count) {
        void* cur_oldroot = tinfo.old_roots[oldroots_idx];
        
        if(roots_idx >= tinfo.roots_count) {
            // Was dropped from roots
            pushPendingDecs(tinfo, cur_oldroot);
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
            pushPendingDecs(tinfo, cur_oldroot);
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
            return ;
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

static void processDecrements(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    GC_REFCT_LOCK_ACQUIRE();
    MEM_STATS_START();

    size_t deccount = 0;
    while(!tinfo.pending_decs.isEmpty() && (deccount < tinfo.max_decrement_count)) {
        void* obj = tinfo.pending_decs.pop_front();

        if (!GC_IS_ALLOCATED(obj)) {
            continue;
        }

        __CoreGC::TypeInfoBase* typeinfo = GC_TYPE(obj);
        if(typeinfo->ptr_mask != PTR_MASK_LEAF) {
            walkPointerMaskForDecrements(tinfo, typeinfo, (void**)obj);
        }

        PageInfo* objects_page = PageInfo::extractPageFromPointer(obj);
        objects_page->pending_decs_count--;

        GC_IS_ALLOCATED(obj) = false;

        if(!GC_IS_ROOT(obj)) {
            DEC_REF_COUNT(obj);
        }

        if(objects_page->seen == false) {
            objects_page->seen = true;
            tinfo.decremented_pages[tinfo.decremented_pages_index++] = objects_page;
        }

        deccount++;
    }

    for(uint32_t i = 0; i < tinfo.decremented_pages_index; i++) {        
        reprocessPageInfo(tinfo.decremented_pages[i], tinfo);
    }
    tinfo.decremented_pages_index = 0;

    MEM_STATS_END(decrement_times);
    GC_REFCT_LOCK_RELEASE();

    //
    //TODO: we want to do a bit of PID controller here on the max decrement count to ensure that we eventually make it back to stable but keep pauses small
    //
}

static void* forward(void* ptr, BSQMemoryTheadLocalInfo& tinfo)
{
    GCAllocator* gcalloc = tinfo.getAllocatorForPageSize(PageInfo::extractPageFromPointer(ptr));
    GC_INVARIANT_CHECK(gcalloc != nullptr);

    __CoreGC::TypeInfoBase* type_info = GC_TYPE(ptr);
    void* nptr = gcalloc->allocateEvacuation(type_info);
    xmem_copy(ptr, nptr, type_info->slot_size);
    updatePointers((void**)nptr, tinfo);

    // Insert into forward table and update object ensuring future objects update
    RESET_METADATA_FOR_OBJECT(GC_GET_META_DATA_ADDR(ptr), tinfo.forward_table_index);
    tinfo.forward_table[tinfo.forward_table_index++] = nptr;

    return nptr;
}

static inline void updateRef(void** obj, BSQMemoryTheadLocalInfo& tinfo)
{
    void* ptr = *obj;
    int fwd_index = GC_FWD_INDEX(ptr);

    if(fwd_index == NON_FORWARDED) {
        // This might me invariant
        if(!GC_IS_ROOT(ptr)) {
            return ;
        }
 
        *obj = forward(ptr, tinfo); 
    }
    else {
        *obj = tinfo.forward_table[fwd_index]; 
    }

    INC_REF_COUNT(*obj);
}

static inline void handleTaggedObjectUpdate(void** slots, BSQMemoryTheadLocalInfo& tinfo) noexcept 
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
static void updatePointers(void** slots, BSQMemoryTheadLocalInfo& tinfo) noexcept
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
static void processMarkedYoungObjects(BSQMemoryTheadLocalInfo& tinfo) noexcept 
{
    GC_REFCT_LOCK_ACQUIRE();
    MEM_STATS_START();

    while(!tinfo.pending_young.isEmpty()) {
        void* obj = tinfo.pending_young.pop_front(); //ensures non-roots visited first
        GC_INVARIANT_CHECK(GC_IS_YOUNG(obj) && GC_IS_MARKED(obj));

        MetaData* m = GC_GET_META_DATA_ADDR(obj);
        updatePointers((void**)obj, tinfo);
        GC_CLEAR_YOUNG_MARK(m);
    }

    MEM_STATS_END(evacuation_times);
    GC_REFCT_LOCK_RELEASE();
}

static void checkPotentialPtr(void* addr, BSQMemoryTheadLocalInfo& tinfo) noexcept
{
    if(addr == nullptr) {
        return ;
    }

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

static void walkStack(BSQMemoryTheadLocalInfo& tinfo) noexcept 
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
    if(meta == nullptr) {
        assert(false);
    }

    if(!GC_SHOULD_VISIT(meta)) {
        return ;
    }
    
    GC_MARK_AS_MARKED(meta);
    tinfo.visit_stack.push_back({*slots, MARK_STACK_NODE_COLOR_GREY});
}

static void handleMarkingTaggedObject(BSQMemoryTheadLocalInfo& tinfo, void** slots) noexcept 
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

        if((typeinfo->ptr_mask == PTR_MASK_LEAF) || (entry.color == MARK_STACK_NODE_COLOR_BLACK)) {
            // No children so do by definition
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

    UPDATE_TOTAL_LIVE_BYTES(gtl_info, =, 0);
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

    MEM_STATS_END(collection_times);
}