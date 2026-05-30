#include "gc.h"

#include "../../core/strings.h"
#include "../../core/list_t.h"

#if GC_INVARIANTS
#define GC_INVARIANT_CHECK(x) assert(x)
#else
#define GC_INVARIANT_CHECK(x)
#endif

#define GC_PTR_IN_RANGE(V) ((GC_MIN_ALLOCATED_ADDRESS <= V) && (V <= GC_MAX_ALLOCATED_ADDRESS))
#define GC_PTR_NOT_IN_STACK(BASE, CURR, V) ((((void*)V) < ((void*)CURR)) || (((void*)BASE) < ((void*)V)))
#define GC_IS_ALIGNED(V) (((uintptr_t)(V) % GC_MEM_ALIGNMENT) == 0)

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
            register void** rbp asm("rbp");
            void** current_frame = rbp;
        
            //Walk the stack
            while (current_frame <= tl_alloc_info.native_stack_base) {
                assert(GC_IS_ALIGNED(current_frame));
            
                //Walk entire frame looking for valid pointers
                void** it = current_frame;
                void* potential_ptr = *it;
                if(GC_PTR_IN_RANGE(potential_ptr) && GC_PTR_NOT_IN_STACK(tl_alloc_info.native_stack_base, current_frame, potential_ptr)) {
                    possibleroots.push_back(potential_ptr);
                }
                it--;
            
                current_frame++;
            }
    

            //Check contents of registers
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, rax)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, rbx)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, rcx)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, rdx)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, rsi)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, rdi)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, r8)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, r9)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, r10)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, r11)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, r12)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, r13)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, r14)
            GC_PROCESS_REGISTER(tl_alloc_info.native_stack_base, current_frame, r15)
        #else
            #error "Architecture not supported"
        #endif
    }

    void processPotentialPtr(void* addr, std::vector<void*>& roots_young, std::vector<void*>& roots_rc)
    { 
        GCMetadata* meta = nullptr;
        void* realaddr = nullptr;
	    if(g_alloc_info.isAllocatedAddress(addr, meta, realaddr)) {
            if(gcIsYoung(meta->rc)) {
                roots_young.push_back(realaddr);
            }
            else {
                roots_rc.push_back(realaddr);
            }
        }
    }

    bool walkGlobalRoots(std::vector<void*>& roots_young, std::vector<void*>& roots_rc)
    {
        std::vector<void*> possibleroots;
        
        bool gproc = g_alloc_info.loadGlobalRootsToProc(possibleroots);
        
        for(auto ii = possibleroots.begin(); ii != possibleroots.end(); ii++) {
            processPotentialPtr(*ii, roots_young, roots_rc);
        }

        return gproc;
    }

    void walkStack(std::vector<void*>& roots_young, std::vector<void*>& roots_rc)
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

    void processRCRoots(std::vector<void*>& roots, std::vector<void*>& finalroots)
    {
        for(size_t i = 0; i < roots.size(); i++) {
            bool alreadyknown = std::binary_search(tl_alloc_info.old_roots.cbegin(), tl_alloc_info.old_roots.cend(), roots[i]);
            if(!alreadyknown) {
                bool keep = gcRootProcessRCIncrement(gcGetMetadata(roots[i])->rc);
                if(keep) {
                    finalroots.push_back(roots[i]);
                }
            }
        }
    }

    void* forward(void* ptr);

    void* processSlotPtrTrgt(void* ptr)
    {
        GCMetadata* m = gcGetMetadata(ptr);
        if(gcIsYoung(m->rc)) {
            return forward(ptr);
        }
        else {
            gcYoungProcessRCIncrement(m->rc);
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
                *slots = processSlotPtrTrgt(*slots);
                tag++;
                slots++;
                break;
            }
            case '2': {
                const TypeInfo* ti = (const TypeInfo*)(*slots);
                tag++;
                slots++;

                const char* mmask = ti->ptrmask;
                while(*mmask == '\0') {
                    processSlotTag(mmask, slots);
                }
                tag += ti->slotcount;
                break;
            }
            case '3': {
                if(!XCString::gcIsTestIsInlineRepresentation(slots)) {
                    *(slots + 1) = processSlotPtrTrgt(*(slots + 1));
                }
                tag += 2;
                slots += 2;
                break;
            }
            case '4': {
                if(!XString::gcIsTestIsInlineRepresentation(slots)) {
                    *(slots + 1) = processSlotPtrTrgt(*(slots + 1));
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
                    *(slots + 1) = processSlotPtrTrgt(*(slots + 1));
                    tag += 2;
                    slots += 2;
                }
                break;
            }
        }
    }

    void* forward(void* ptr)
    {
        GCMetadata* m = gcGetMetadata(ptr); 

        if(gcIsForwarded(m->rc)) {
            return *((void**)ptr);
        }
        else {
            GCAllocatorImpl* gcalloc = gcGetAllocator<GCAllocatorImpl>(ptr);
            const TypeInfo* ti = gcGetTypeInfo(ptr);

            void* nptr = gcalloc->xalloc_evac(); 
	        std::copy((void**)ptr, (void**)ptr + ti->slotcount, (void**)nptr);

            if(ti->ptrmask != nullptr) {
                const char* mmask = ti->ptrmask;
                void** slots = (void**)nptr;
                while(*mmask == '\0') {
                    processSlotTag(mmask, slots);
                }
            }

            gcProcessUpdateYoungForward(m->rc);
            return nptr;
        }
    }

    void processYoungRoots(std::vector<void*>& roots)
    {
        for(size_t i = 0; i < roots.size(); i++) {
            gcRootProcessYoungPromote(gcGetMetadata(roots[i])->rc);
        }

        for(size_t i = 0; i < roots.size(); i++) {
            const TypeInfo* ti = gcGetTypeInfo(roots[i]);

            if(ti->ptrmask != nullptr) {
                const char* mmask = ti->ptrmask;
                void** slots = (void**)roots[i];
                while(*mmask == '\0') {
                    processSlotTag(mmask, slots);
                }
            }
        }
    }

    void processDecrements(const std::vector<void*>& roots_young, const std::vector<void*>& roots_rc)
    {
        //TODO: need to process the decrements and update the roots sets for the next collection round
        return;
    }

    void collect()
    {
        std::vector<void*> curr_roots_young;
        std::vector<void*> curr_roots_rc;
        std::vector<void*> final_roots_rc;
        curr_roots_young.reserve(128); //TODO -- tune this
        curr_roots_rc.reserve(128); //TODO -- tune this

        bool gproc = false;
        {
            // page->entrycount may be reset by another thread (setPageMetaData) -- processPotentialPtr
	        std::lock_guard lk(g_alloc_info.g_pages_mutex);

            gproc = walkGlobalRoots(curr_roots_young, curr_roots_rc);
            walkStack(curr_roots_young, curr_roots_rc);

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
        
        //Process decrements and update the roots info for the next round
        processDecrements(curr_roots_young, final_roots_rc);

        //Make sure we release the globals mutex if needed
        g_alloc_info.unloadGlobalRootsFromProc(gproc);
    }
}
