#include "gc.h"

#include "../../core/strings.h"
#include "../../core/list_t.h"

#if GC_INVARIANTS
#define GC_INVARIANT_CHECK(x) assert(x)
#else
#define GC_INVARIANT_CHECK(x)
#endif

#define GC_PTR_IN_RANGE(V) ((GC_MIN_ALLOCATED_ADDRESS <= V) && (V <= GC_MAX_ALLOCATED_ADDRESS))
#define GC_PTR_NOT_IN_STACK(BASE, CURR, V) ((((void*)V) <= ((void*)CURR)) || (((void*)BASE) <= ((void*)V)))

#define GC_PROCESS_REGISTER(BASE, CURR, R)                                    \
    register void* R asm(#R);                                                 \
    rcontents.R = NULL;                                        \
    if(GC_PTR_IN_RANGE(R) && GC_PTR_NOT_IN_STACK(BASE, CURR, R)) { rcontents.R = R; }

namespace ᐸRuntimeᐳ
{
    void loadNativeRootSet(RegisterContents& rcontents, std::vector<void*>& possibleroots)
    {
        //this code should load from the asm stack pointers and copy the native stack into the roots memory
        #ifdef __x86_64__
            void** rbp = (void**)__builtin_frame_address(0);
            void** iter = rbp;
        
            //Walk the stack
            while (iter <= tl_alloc_info.native_stack_base) {
                void* potential_ptr = *iter;
                if(GC_PTR_IN_RANGE(potential_ptr) && GC_PTR_NOT_IN_STACK(tl_alloc_info.native_stack_base, rbp, potential_ptr)) {
                    possibleroots.push_back(potential_ptr);
                }
                iter++;
            }
    
            //Check contents of registers
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, rax)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, rbx)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, rcx)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, rdx)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, rsi)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, rdi)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, r8)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, r9)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, r10)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, r11)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, r12)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, r13)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, r14)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, rbp, r15)
        #else
            #error "Architecture not supported"
        #endif
    }

    constexpr static auto RootCmp = [](const std::pair<AtomicGCMetadata*, void*>& a, const std::pair<AtomicGCMetadata*, void*>& b) {
        return a.second < b.second;
    };

    void processPotentialPtr(void* addr, std::vector<std::pair<AtomicGCMetadata*, void*>>& roots_young, std::vector<std::pair<AtomicGCMetadata*, void*>>& roots_rc)
    { 
        AtomicGCMetadata* meta = nullptr;
        void* realaddr = nullptr;
	    if(g_alloc_info.isAllocatedAddress(addr, meta, realaddr)) {
            if(gcIsYoung(meta)) {
                roots_young.push_back(std::make_pair(meta, realaddr));
            }
            else {
                roots_rc.push_back(std::make_pair(meta, realaddr));
            }
        }
    }

    bool walkGlobalRoots(std::vector<std::pair<AtomicGCMetadata*, void*>>& roots_young, std::vector<std::pair<AtomicGCMetadata*, void*>>& roots_rc)
    {
        std::vector<void*> possibleroots;
        
        bool gproc = g_alloc_info.loadGlobalRootsToProc(possibleroots);
        
        for(auto ii = possibleroots.begin(); ii != possibleroots.end(); ii++) {
            processPotentialPtr(*ii, roots_young, roots_rc);
        }

        return gproc;
    }

    void walkStack(std::vector<std::pair<AtomicGCMetadata*, void*>>& roots_young, std::vector<std::pair<AtomicGCMetadata*, void*>>& roots_rc)
    {
        RegisterContents rcontents{};

        std::vector<void*> possibleroots;
        possibleroots.reserve(256); //TODO -- tune this

        loadNativeRootSet(rcontents, possibleroots);
        
        roots_young.reserve(possibleroots.size() / 4); //TODO -- tune this
        roots_rc.reserve(possibleroots.size() / 4); //TODO -- tune this

        for(auto ii = possibleroots.begin(); ii != possibleroots.end(); ii++) {
            processPotentialPtr(*ii, roots_young, roots_rc);
        }

        processPotentialPtr(rcontents.rax, roots_young, roots_rc);
        processPotentialPtr(rcontents.rbx, roots_young, roots_rc);
        processPotentialPtr(rcontents.rcx, roots_young, roots_rc);
        processPotentialPtr(rcontents.rdx, roots_young, roots_rc);
        processPotentialPtr(rcontents.rsi, roots_young, roots_rc);
        processPotentialPtr(rcontents.rdi, roots_young, roots_rc);
        processPotentialPtr(rcontents.r8, roots_young, roots_rc);
        processPotentialPtr(rcontents.r9, roots_young, roots_rc);
        processPotentialPtr(rcontents.r10, roots_young, roots_rc);
        processPotentialPtr(rcontents.r11, roots_young, roots_rc);
        processPotentialPtr(rcontents.r12, roots_young, roots_rc);
        processPotentialPtr(rcontents.r13, roots_young, roots_rc);
        processPotentialPtr(rcontents.r14, roots_young, roots_rc);
        processPotentialPtr(rcontents.r15, roots_young, roots_rc);
    }

    void processRCRoots(std::vector< std::pair<AtomicGCMetadata*, void*>>& roots, std::vector<std::pair<AtomicGCMetadata*, void*>>& finalroots)
    {
        for(size_t i = 0; i < roots.size(); i++) {
            bool alreadyknown = std::binary_search(tl_alloc_info.old_roots.cbegin(), tl_alloc_info.old_roots.cend(), roots[i], RootCmp);
            
            if(alreadyknown) {
                finalroots.push_back(roots[i]);
            }
            else {
                GC_DIAG_LEVEL_2_OP(g_memstats.processrootinc(roots[i].second));
                bool keep = gcRootProcessRCIncrement(roots[i].first);
                if(keep) {
                    finalroots.push_back(roots[i]);
                }
            }
        }
    }

    void* forward(AtomicGCMetadata* m, void* ptr, void** parentslotptr);

    void* processSlotPtrTrgt(void* ptr, void** parentslotptr)
    {
        if(ptr == nullptr) {
            return nullptr;
        }

        AtomicGCMetadata* m = gcGetMetadata(ptr);
        if(gcIsYoung(m)) {
            return forward(m, ptr, parentslotptr);
        }
        else {
            GC_DIAG_LEVEL_2_OP(g_memstats.processstdinc(ptr));
            gcYoungProcessRCIncrement(m);
            return ptr;
        }
    }

    void processSlotTag(const char*& tag, void**& slots) {
        switch(*tag) {
            case '0': {
                tag++;
                slots++;
                break;
            }
            case '1': {
                *slots = processSlotPtrTrgt(*slots, slots);
                tag++;
                slots++;
                break;
            }
            case '2': {
                const TypeInfo* ti = (const TypeInfo*)(*slots);
                tag++;
                slots++;

                if(ti != nullptr) {
                    const char* mmask = ti->ptrmask;
                    while(*mmask != '\0') {
                        processSlotTag(mmask, slots);
                    }
                    tag += ti->slotcount;
                }
                break;
            }
            case '3': {
                if(!XCString::gcIsTestIsInlineRepresentation(slots)) {
                    *(slots + 1) = processSlotPtrTrgt(*(slots + 1), slots + 1);
                }
                tag += 2;
                slots += 2;
                break;
            }
            case '4': {
                if(!XString::gcIsTestIsInlineRepresentation(slots)) {
                    *(slots + 1) = processSlotPtrTrgt(*(slots + 1), slots + 1);
                }
                tag += 2;
                slots += 2;
                break;
            }
            case '5' : {
                if(gcIsListTInline(slots)) {
                    //inline then ptrmask is already inline so just eat the '5' -- otherwise process the pointer and return 2
                    tag++;
                    slots++;
                }
                else {
                    *(slots + 1) = processSlotPtrTrgt(*(slots + 1), slots + 1);
                    tag += 2;
                    slots += 2;
                }
                break;
            }
        }
    }

    void* forward(AtomicGCMetadata* m, void* ptr, void** parentslotptr)
    {
        if(gcIsForwarded(m)) {
            return *((void**)ptr);
        }
        else {
            GC_DIAG_LEVEL_2_OP(g_memstats.processpromotion(ptr, false));
            GCAllocatorImpl* gcalloc = gcGetAllocator(ptr);

            void* nptr = gcalloc->xalloc_evac(parentslotptr); 
	        std::copy((void**)ptr, (void**)ptr + gcalloc->alloctype->slotcount, (void**)nptr);

            *((void**)ptr) = nptr;
            gcProcessUpdateYoungForward(m);

            if(gcalloc->alloctype->ptrmask != nullptr) {
                const char* mmask = gcalloc->alloctype->ptrmask;
                void** slots = (void**)nptr;
                while(*mmask != '\0') {
                    processSlotTag(mmask, slots);
                }
            }

            return nptr;
        }
    }

    void processYoungRoots(std::vector<std::pair<AtomicGCMetadata*, void*>>& roots)
    {
        for(size_t i = 0; i < roots.size(); i++) {
            GC_DIAG_LEVEL_2_OP(g_memstats.processpromotion(roots[i].second, true));
            gcRootProcessYoungPromote(roots[i].first);
        }

        //
        //TODO: This processing is recursive on the object graph -- so OOS is definitely a concern at some point
        //      We will want to make this a loop with an explicit stack to avoid these issues at some point but for now we are just using a simple recursive implementation 
        //
        for(size_t i = 0; i < roots.size(); i++) {
            const TypeInfo* ti = gcGetTypeInfo(roots[i].second);

            if(ti->ptrmask != nullptr) {
                const char* mmask = ti->ptrmask;
                void** slots = (void**)roots[i].second;
                while(*mmask != '\0') {
                    processSlotTag(mmask, slots);
                }
            }
        }
    }

    void releaseQuick(void* ptr);

    void decrementQuickSlotTag(const char*& tag, void**& slots) {
        switch(*tag) {
            case '0': {
                tag++;
                slots++;
                break;
            }
            case '1': {
                if(*slots != nullptr) {
                    GC_DIAG_LEVEL_2_OP(g_memstats.processstddec(*slots));
                    bool isdead = gcProcessRCDecrement(gcGetMetadata(*slots));
                    if(isdead) {
                        releaseQuick(*slots);
                    }
                }
                tag++;
                slots++;
                break;
            }
            case '2': {
                const TypeInfo* ti = (const TypeInfo*)(*slots);
                tag++;
                slots++;

                if(ti != nullptr) {
                    const char* mmask = ti->ptrmask;
                    while(*mmask != '\0') {
                        decrementQuickSlotTag(mmask, slots);
                    }
                    tag += ti->slotcount;
                }
                break;
            }
            //other cases should not be possible in a quick release object since they are all leaf types
        }
    }

    void releaseQuick(void* ptr)
    {
        GCAllocatorImpl* alloc = gcGetAllocator(ptr);
        const TypeInfo* ti = alloc->alloctype;   
        if(ti->ptrmask != nullptr) {
            const char* mmask = ti->ptrmask;
            void** slots = (void**)ptr;
            while(*mmask != '\0') {
                decrementQuickSlotTag(mmask, slots);
            }
        }

        GC_DIAG_LEVEL_2_OP(g_memstats.processreclaimrc(ptr));
        alloc->xrcRelease(ptr);
    }
    
    void releaseStd(void* ptr)
    {
        const TypeInfo* ti = gcGetTypeInfo(ptr);
        if(ti->quickrelease) {
             releaseQuick(ptr);
        }
        else {
            GC_DIAG_LEVEL_2_OP(g_memstats.processpushpendingdelete(ptr));
            /*
            gcStoreDeleteListPtr(gcGetMetadata(ptr), tl_alloc_info.pendingdelete);
            tl_alloc_info.pendingdelete = ptr;
            */

            assert(std::find(tl_alloc_info.pendingdelete.cbegin(), tl_alloc_info.pendingdelete.cend(), ptr) == tl_alloc_info.pendingdelete.cend());
            tl_alloc_info.pendingdelete.push_back(ptr);
        }
    }

    void decrementStdSlotTag(const char*& tag, void**& slots) {
        switch(*tag) {
            case '0': {
                tag++;
                slots++;
                break;
            }
            case '1': {
                if(*slots != nullptr) {
                    GC_DIAG_LEVEL_2_OP(g_memstats.processstddec(*slots));
                    bool isdead = gcProcessRCDecrement(gcGetMetadata(*slots));
                    if(isdead) {
                        releaseStd(*slots);
                    }
                }
                tag++;
                slots++;
                break;
            }
            case '2': {
                const TypeInfo* ti = (const TypeInfo*)(*slots);
                tag++;
                slots++;

                if(ti != nullptr) {
                    const char* mmask = ti->ptrmask;
                    while(*mmask != '\0') {
                        decrementStdSlotTag(mmask, slots);
                    }
                    tag += ti->slotcount;
                }
                break;
            }
            case '3': {
                if(!XCString::gcIsTestIsInlineRepresentation(slots)) {
                    GC_DIAG_LEVEL_2_OP(g_memstats.processstddec(*(slots + 1)));
                    bool isdead = gcProcessRCDecrement(gcGetMetadata(*(slots + 1)));
                    if(isdead) {
                        releaseStd(*(slots + 1));
                    }
                }
                tag += 2;
                slots += 2;
                break;
            }
            case '4': {
                if(!XString::gcIsTestIsInlineRepresentation(slots)) {
                    GC_DIAG_LEVEL_2_OP(g_memstats.processstddec(*(slots + 1)));
                    bool isdead = gcProcessRCDecrement(gcGetMetadata(*(slots + 1)));
                    if(isdead) {
                        releaseStd(*(slots + 1));
                    }
                }
                tag += 2;
                slots += 2;
                break;
            }
            case '5' : {
                if(gcIsListTInline(slots)) {
                    //inline then ptrmask is already inline so just eat the '5' -- otherwise process the pointer and return 2
                    tag++;
                    slots++;
                }
                else {
                    GC_DIAG_LEVEL_2_OP(g_memstats.processstddec(*(slots + 1)));
                    bool isdead = gcProcessRCDecrement(gcGetMetadata(*(slots + 1)));
                    if(isdead) {
                        releaseStd(*(slots + 1));
                    }
                    tag += 2;
                    slots += 2;
                }
                break;
            }
        }
    }

    void processDecrements(const std::vector<std::pair<AtomicGCMetadata*, void*>>& roots_young, const std::vector<std::pair<AtomicGCMetadata*, void*>>& roots_rc)
    {
        std::vector<std::pair<AtomicGCMetadata*, void*>> decroots;
        std::copy_if(tl_alloc_info.old_roots.cbegin(), tl_alloc_info.old_roots.cend(), std::back_inserter(decroots), [&roots_young, &roots_rc](const std::pair<AtomicGCMetadata*, void*>& r) {
            return !std::binary_search(roots_young.cbegin(), roots_young.cend(), r, RootCmp) && !std::binary_search(roots_rc.cbegin(), roots_rc.cend(), r, RootCmp);
        });
        
        for(size_t i = 0; i < decroots.size(); i++) {
            GC_DIAG_LEVEL_2_OP(g_memstats.processrootdec(decroots[i].second));

            auto [meta, droot] = decroots[i];
            bool isdead = gcProcessRCDecrement(meta);

            if(isdead) {
                const TypeInfo* ti = gcGetTypeInfo(droot);
                if(ti->quickrelease) {
                    releaseQuick(droot);
                }
                else {
                    releaseStd(droot);
                }
            }
        }
        
        tl_alloc_info.old_roots.resize(roots_young.size() + roots_rc.size());
        std::merge(roots_young.cbegin(), roots_young.cend(), roots_rc.cbegin(), roots_rc.cend(), tl_alloc_info.old_roots.begin(), RootCmp);
    }

    void processPendingDeleteWork(size_t worklimit)
    {
        size_t procbytes = 0;
        auto iter = tl_alloc_info.pendingdelete.begin();
        while(iter != tl_alloc_info.pendingdelete.end()) {
            /*
            void* ptr = alloc->pendingdelete;
            alloc->pendingdelete = gcGetDeleteListPtr(gcGetMetadata(ptr));
            */
            void* ptr = tl_alloc_info.pendingdelete.front();
            tl_alloc_info.pendingdelete.pop_front();

            GCAllocatorImpl* alloc = gcGetAllocator(ptr);
            if(alloc->alloctype->ptrmask != nullptr) {
                const char* mmask = alloc->alloctype->ptrmask;
                void** slots = (void**)ptr;
                while(*mmask != '\0') {
                    decrementStdSlotTag(mmask, slots);
                }
            }

            GC_DIAG_LEVEL_2_OP(g_memstats.processreclaimrc(ptr));
            alloc->xrcRelease(ptr);

            procbytes += alloc->alloctype->bytesize;
            if(procbytes >= worklimit) {
                break;
            }
        }
    }

    template <bool skipwalk>
    void xcollect(std::initializer_list<void*> yroots, std::initializer_list<void*> rcroots)
    {
        std::vector<std::pair<AtomicGCMetadata*, void*>> curr_roots_young;
        std::vector<std::pair<AtomicGCMetadata*, void*>> curr_roots_rc;
        std::vector<std::pair<AtomicGCMetadata*, void*>> final_roots_rc;
        curr_roots_young.reserve(128); //TODO -- tune this
        curr_roots_rc.reserve(128); //TODO -- tune this

        GC_DIAG_LEVEL_1_OP(auto time_collect_start = std::chrono::high_resolution_clock::now());
        bool gproc = false;
        {
            // page->entrycount may be reset by another thread (setPageMetaData) -- processPotentialPtr
	        std::lock_guard lk(g_alloc_info.g_pages_mutex);

            if constexpr (skipwalk) {
                std::transform(yroots.begin(), yroots.end(), std::back_inserter(curr_roots_young), [](void* ptr) {
                    return std::make_pair(gcGetMetadata(ptr), ptr);
                });
                std::transform(rcroots.begin(), rcroots.end(), std::back_inserter(curr_roots_rc), [](void* ptr) {
                    return std::make_pair(gcGetMetadata(ptr), ptr);
                });
            }
            else {
                gproc = walkGlobalRoots(curr_roots_young, curr_roots_rc);
                walkStack(curr_roots_young, curr_roots_rc);
            }

            std::sort(curr_roots_young.begin(), curr_roots_young.end());
            curr_roots_young.erase(std::unique(curr_roots_young.begin(), curr_roots_young.end()), curr_roots_young.end());

            std::sort(curr_roots_rc.begin(), curr_roots_rc.end());
            curr_roots_rc.erase(std::unique(curr_roots_rc.begin(), curr_roots_rc.end()), curr_roots_rc.end());

            //Handle the RC roots 
            final_roots_rc.reserve(curr_roots_rc.size());
            processRCRoots(curr_roots_rc, final_roots_rc);
        }

        //Handle the young roots + the young walk and evacuation
        processYoungRoots(curr_roots_young);
        
        GC_DIAG_LEVEL_1_OP(auto time_collect_traverse_end = std::chrono::high_resolution_clock::now());

        //Process decrements and update the roots info for the next round
        processDecrements(curr_roots_young, final_roots_rc);

        //Make sure we release the globals mutex if needed
        g_alloc_info.unloadGlobalRootsFromProc(gproc);

        //Peel off some of the pending decs
        processPendingDeleteWork(GC_DELETE_PENDING_PROCESS_BYTES_COLLECT);
        
        GC_DIAG_LEVEL_1_OP(auto time_collect_rc_end = std::chrono::high_resolution_clock::now());

        //Process nursery space
        for(auto ai = tl_alloc_info.gcallocs.begin(); ai != tl_alloc_info.gcallocs.end(); ++ai) {
            //TODO: we may want a list of nurserys that are dirty here -- that way we only visit with allocs to process instead of everyone (which may matter on larger programs)
            ai->second->processNursery();
        }

        GC_DIAG_LEVEL_1_OP(auto time_collect_end = std::chrono::high_resolution_clock::now());
        GC_DIAG_LEVEL_1_OP(g_memstats.processcollect(MemStats::time_in_millis(time_collect_end - time_collect_start), MemStats::time_in_millis(time_collect_traverse_end - time_collect_start), MemStats::time_in_millis(time_collect_rc_end - time_collect_traverse_end)));
    }

    void collect()
    {
        xcollect<false>({}, {});
    }

    void test_collect(std::initializer_list<void*> yroots, std::initializer_list<void*> rcroots)
    {
        xcollect<true>(yroots, rcroots);
    }
}
