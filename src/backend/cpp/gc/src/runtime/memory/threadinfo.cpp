#include "threadinfo.h"

thread_local void* roots_array[BSQ_MAX_ROOTS];
thread_local void* old_roots_array[BSQ_MAX_ROOTS];
thread_local void* forward_table_array[BSQ_MAX_FWD_TABLE_ENTRIES];

thread_local GCAllocator* g_gcallocs_array[BSQ_MAX_ALLOC_SLOTS];

thread_local BSQMemoryTheadLocalInfo gtl_info;

#define PTR_IN_RANGE(V) ((MIN_ALLOCATED_ADDRESS <= V) && (V <= MAX_ALLOCATED_ADDRESS))
#define PTR_NOT_IN_STACK(BASE, CURR, V) ((((void*)V) < ((void*)CURR)) || (((void*)BASE) < ((void*)V)))
#define IS_ALIGNED(V) (((uintptr_t)(V) % sizeof(void*)) == 0)

#define PROCESS_REGISTER(BASE, CURR, R)                                       \
    register void* R asm(#R);                                                 \
    native_register_contents.R = NULL;                                        \
    if(PTR_IN_RANGE(R) && PTR_NOT_IN_STACK(BASE, CURR, R)) { native_register_contents.R = R; }

void BSQMemoryTheadLocalInfo::initialize(size_t ntl_id, void** caller_rbp, 
	void (*_collectfp)()) noexcept
{
    assert(caller_rbp != nullptr);
   	assert(_collectfp != nullptr);

	this->collectfp = _collectfp;

    this->tl_id = ntl_id;
    this->native_stack_base = caller_rbp;

    this->roots = roots_array;
    this->roots_count = 0;
    xmem_zerofill(this->roots, BSQ_MAX_ROOTS);

    this->old_roots = old_roots_array;
    this->old_roots_count = 0;
    xmem_zerofill(this->old_roots, BSQ_MAX_ROOTS);

    this->forward_table = forward_table_array;
    this->forward_table_index = FWD_TABLE_START;
    xmem_zerofill(this->forward_table, BSQ_MAX_FWD_TABLE_ENTRIES);

    this->g_gcallocs = g_gcallocs_array;
    xmem_zerofill(this->g_gcallocs, BSQ_MAX_ALLOC_SLOTS);
}

void BSQMemoryTheadLocalInfo::loadNativeRootSet() noexcept
{
    this->native_stack_contents.initialize();

    //this code should load from the asm stack pointers and copy the native stack into the roots memory
    #ifdef __x86_64__
        register void** rbp asm("rbp");
        void** current_frame = rbp;
        
        /* Walk the stack */
        while (current_frame <= native_stack_base) {
            assert(IS_ALIGNED(current_frame));
            
            /* Walk entire frame looking for valid pointers */
            void** it = current_frame;
            void* potential_ptr = *it;
            if (PTR_IN_RANGE(potential_ptr) && PTR_NOT_IN_STACK(native_stack_base, current_frame, potential_ptr)) {
                this->native_stack_contents.push_back(potential_ptr);
            }
            it--;
            
            current_frame++;
        }
    

        /* Check contents of registers */
        PROCESS_REGISTER(native_stack_base, current_frame, rax)
        PROCESS_REGISTER(native_stack_base, current_frame, rbx)
        PROCESS_REGISTER(native_stack_base, current_frame, rcx)
        PROCESS_REGISTER(native_stack_base, current_frame, rdx)
        PROCESS_REGISTER(native_stack_base, current_frame, rsi)
        PROCESS_REGISTER(native_stack_base, current_frame, rdi)
        PROCESS_REGISTER(native_stack_base, current_frame, r8)
        PROCESS_REGISTER(native_stack_base, current_frame, r9)
        PROCESS_REGISTER(native_stack_base, current_frame, r10)
        PROCESS_REGISTER(native_stack_base, current_frame, r11)
        PROCESS_REGISTER(native_stack_base, current_frame, r12)
        PROCESS_REGISTER(native_stack_base, current_frame, r13)
        PROCESS_REGISTER(native_stack_base, current_frame, r14)
        PROCESS_REGISTER(native_stack_base, current_frame, r15)
    #else
        #error "Architecture not supported"
    #endif
}

void BSQMemoryTheadLocalInfo::unloadNativeRootSet() noexcept
{
    this->native_stack_contents.clear();
}

void BSQMemoryTheadLocalInfo::cleanup() noexcept
{ 
	// TODO need a lock here!
	// Run a collection to update thread counts	
    bool prev = g_disable_stack_refs;
	g_disable_stack_refs = true;
#ifdef BSQ_GC_TESTING 
    g_thd_testing = false;
#endif
    this->collectfp();
    g_disable_stack_refs = prev;
#ifdef BSQ_GC_TESTING 
    g_thd_testing = true;
#endif
}


