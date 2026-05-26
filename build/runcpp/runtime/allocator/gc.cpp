#include "gc.h"

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
    struct MarkStackEntry
    {
        void* obj;
        uintptr_t color;
    };
    
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

    bool processPotentialPtr(void* addr, std::vector<void*>& roots_young, std::vector<void*>& roots_rc)
    { 
        GCMetadata* meta = nullptr;
        void* realaddr = nullptr;
	    if(g_alloc_info.isAllocatedAddress(addr, meta, realaddr)) {
            if(meta->isyoung) {
                roots_young.push_back(realaddr);
            }
            else {
                roots_rc.push_back(realaddr);
            }
            
            return meta->threadid == std::this_thread::get_id();
        }

        return false;
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

    bool walkStack(std::vector<void*>& roots_young, std::vector<void*>& roots_rc)
    {
        RegisterContents rcontents{};

        std::vector<void*> possibleroots;
        possibleroots.reserve(256); //TODO -- tune this

        loadNativeRootSet(rcontents, possibleroots);

        // page->entrycount may be reset by another thread (setPageMetaData) -- processPotentialPtr
	    std::lock_guard lk(g_alloc_info.g_pages_mutex);
        
        bool maybecrazyroot = false;
        roots_young.reserve(possibleroots.size() / 4); //TODO -- tune this
        roots_rc.reserve(possibleroots.size() / 4); //TODO -- tune this

        for(auto ii = possibleroots.begin(); ii != possibleroots.end(); ii++) {
            maybecrazyroot |= processPotentialPtr(*ii, roots_young, roots_rc);
        }

        maybecrazyroot |= processPotentialPtr(rcontents.rax, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.rbx, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.rcx, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.rdx, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.rsi, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.rdi, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.r8, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.r9, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.r10, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.r11, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.r12, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.r13, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.r14, roots_young, roots_rc);
        maybecrazyroot |= processPotentialPtr(rcontents.r15, roots_young, roots_rc);

        return maybecrazyroot;
    }

    void processRCRoots(std::vector<void*>& roots)
    {
        return;
    }

    void collect()
    {
        std::vector<void*> curr_roots_young;
        std::vector<void*> curr_roots_rc;
        curr_roots_young.reserve(128); //TODO -- tune this
        curr_roots_rc.reserve(128); //TODO -- tune this

        bool gproc = walkGlobalRoots(curr_roots_young, curr_roots_rc);
        bool maybecrazyroot = walkStack(curr_roots_young, curr_roots_rc);

        //TODO -- if maybecrazyroot then need to critical section with decs and other stack walkers
        //     -- later assume that if gproc is true then we should do the crazy root path too -- just for safety/simplicity!!!
        assert(!maybecrazyroot);

        xxxx;
        //TODO -- handle the RC roots (these can't trigger any walk or evacuation)

        //TODO -- handle the young roots + the young walk and evacuation
        assert(false);

        //TODO -- process Decs

        //Make sure we release the globals mutex if needed
        g_alloc_info.unloadGlobalRootsFromProc(gproc);
    }
}
