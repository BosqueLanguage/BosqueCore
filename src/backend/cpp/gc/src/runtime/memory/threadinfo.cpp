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

void BSQMemoryTheadLocalInfo::initialize(size_t tl_id, void** caller_rbp) noexcept
{
    this->tl_id = tl_id;
    this->native_stack_base = caller_rbp;

    this->roots = roots_array;
    this->roots_count = 0;
    xmem_zerofill(this->roots, BSQ_MAX_ROOTS);

    this->old_roots = old_roots_array;
    this->old_roots_count = 0;
    xmem_zerofill(this->old_roots, BSQ_MAX_ROOTS);

    this->forward_table = forward_table_array;
    this->forward_table_index = 0;
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

#ifdef MEM_STATS

// Overflow in this calculation IS possible so we need to be careful if we are
// running very long tests
double compute_average_time(uint64_t buckets[MAX_MEMSTATS_BUCKETS]) noexcept
{
    double sum = 0.0;
    double avg = BUCKET_AVERAGE;
    uint64_t count = 0;

    for(int i = 0; i < MAX_MEMSTATS_BUCKETS - 1; i++) {
        uint64_t nentries = buckets[i];
        if(nentries != 0) {
            sum += nentries * avg;
            count += nentries;
        }
        avg += BUCKET_VARIANCE;
    }

    return sum / count;
}

std::string generate_bucket_data(uint64_t buckets[MAX_MEMSTATS_BUCKETS]) noexcept 
{
    std::string buf = "[";
    for(int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        std::string ndata = std::to_string(buckets[i]);
        if(i != MAX_MEMSTATS_BUCKETS - 1) {
            ndata += ", ";
        }
        
        buf += ndata;    
    }
    return buf + "]\n";
}

//
// Spits out contents of each bucket in a format like so: 
// {Bucket Variance, Number of Buckets}
// <Statistic Name>[data, data, data]
// <Statistic Name>[data, data, data] ...
//
std::string generate_formatted_memstats(MemStats& ms) noexcept
{
    std::string header = "{" + std::to_string(BUCKET_VARIANCE) 
        + ", " + std::to_string(MAX_MEMSTATS_BUCKETS) + "}\n";

    std::string collection_data = generate_bucket_data(ms.collection_times);
    std::string collection_times = "<Collection Times>" + collection_data;

    std::string marking_data = generate_bucket_data(ms.marking_times);
    std::string marking_times = "<Marking Times>" + marking_data;

    std::string evacuation_data = generate_bucket_data(ms.evacuation_times);
    std::string evacuation_times = "<Evacuation Times>" + evacuation_data;

    std::string decrement_data = generate_bucket_data(ms.decrement_times);
    std::string decrement_times = "<Decrement Times>" + decrement_data;

    return header + collection_times + marking_times
        + evacuation_times + decrement_times;
}

#endif //MEM_STATS