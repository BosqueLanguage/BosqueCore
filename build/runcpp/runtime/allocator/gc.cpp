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

    bool pointsToObjectStart(void* addr) noexcept 
    {
        uintptr_t offset = reinterpret_cast<uintptr_t>(addr) & GC_PAGE_MASK; 
        PageInfo* p = PageInfo::extractPageFromPointer(addr);
	    if(offset < (sizeof(PageInfo) + METADATA_SEG_SIZE(p))) {
            return false;
        }

        uintptr_t start = GET_SLOT_START_FROM_OFFSET(offset, p);
        return start % p->realsize == 0;
    }

    bool processPotentialPtr(void* addr, std::vector<void*>& roots)
    { 
	    if(!GlobalPageGCManager::g_gc_page_manager.pagetableQuery(addr) || !pointsToObjectStart(addr))
	    {
            return false;
        }

    	GCMetaData* m = PageInfo::getObjectMetadataAligned(addr);
	    if(!GC_IS_ALLOCATED(m)) {
		    return false;
	    }

        roots.push_back(addr);
    }

    void walkStack(std::vector<void*>& roots)
    {
        RegisterContents rcontents{};

        std::vector<void*> possibleroots;
        possibleroots.reserve(512); //TODO -- tune this

        loadNativeRootSet(rcontents, possibleroots);

        std::vector<void*> roots;
        roots.reserve(possibleroots.size() / 4); //TODO -- tune this

        // page->entrycount may be reset by another thread (setPageMetaData) -- processPotentialPtr
	    std::lock_guard lk(g_alloc_info.g_pages_mutex);
        
        for(auto ii = possibleroots.begin(); ii != possibleroots.end(); ii++) {
            processPotentialPtr(*ii, roots);
        }

        processPotentialPtr(rcontents.rax, roots);
        processPotentialPtr(rcontents.rbx, roots);
        processPotentialPtr(rcontents.rcx, roots);
        processPotentialPtr(rcontents.rdx, roots);
        processPotentialPtr(rcontents.rsi, roots);
        processPotentialPtr(rcontents.rdi, roots);
        processPotentialPtr(rcontents.r8, roots);
        processPotentialPtr(rcontents.r9, roots);
        processPotentialPtr(rcontents.r10, roots);
        processPotentialPtr(rcontents.r11, roots);
        processPotentialPtr(rcontents.r12, roots);
        processPotentialPtr(rcontents.r13, roots);
        processPotentialPtr(rcontents.r14, roots);
        processPotentialPtr(rcontents.r15, roots);
    }

    void collect()
    {
        std::vector<void*> curr_roots{};
        curr_roots.reserve(256); //TODO -- tune this

        //TODO: do we need a lock here around roots & RC????
        //E.g. what if I find a false root to another threads young object! Or RC object that they are just collecting  

        bool gproc = g_alloc_info.loadGlobalRootsToProc(curr_roots);
        walkStack(curr_roots);

        //TODO -- more stuff!!!!
        assert(false);

        //Make sure we release the globals mutex if needed
        g_alloc_info.unloadGlobalRootsFromProc(gproc);
    }
}
