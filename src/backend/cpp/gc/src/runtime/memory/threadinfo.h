#pragma once 

#include "allocator.h"

#define InitBSQMemoryTheadLocalInfo() { ALLOC_LOCK_ACQUIRE(); register void** rbp asm("rbp"); gtl_info.initialize(GlobalThreadAllocInfo::s_thread_counter++, rbp); ALLOC_LOCK_RELEASE(); }

#define MAX_ALLOC_LOOKUP_TABLE_SIZE 1024

#define MARK_STACK_NODE_COLOR_GREY 0
#define MARK_STACK_NODE_COLOR_BLACK 1

#define FWD_TABLE_START 1

struct MarkStackEntry
{
    void* obj;
    uintptr_t color;
};

struct RegisterContents
{
    //Should never have pointers of interest in these
    //void* rbp;
    //void* rsp;

    void* rax = nullptr;
    void* rbx = nullptr;
    void* rcx = nullptr;
    void* rdx = nullptr;
    void* rsi = nullptr;
    void* rdi = nullptr;
    void* r8 = nullptr;
    void* r9 = nullptr;
    void* r10 = nullptr;
    void* r11 = nullptr;
    void* r12 = nullptr;
    void* r13 = nullptr;
    void* r14 = nullptr;
    void* r15 = nullptr;
};

#ifdef MEM_STATS

// Buckets store BUCKET_VARIANCE ms variance, final entry is for outliers (hopefully never any values present there)
#define MAX_MEMSTATS_BUCKETS 100 + 1
struct MemStats {
    size_t total_alloc_count  = 0;
    size_t total_alloc_memory = 0;

    size_t total_collections = 0;

    double min_collection_time = 0;
    double max_collection_time = 0;    

    size_t max_live_heap = 0;

    size_t collection_times[MAX_MEMSTATS_BUCKETS] { 0 };
    size_t marking_times[MAX_MEMSTATS_BUCKETS]    { 0 };
    size_t evacuation_times[MAX_MEMSTATS_BUCKETS] { 0 };
    size_t decrement_times[MAX_MEMSTATS_BUCKETS]  { 0 };
};
#else
struct MemStats {};
#endif

//All of the data that a thread local allocator needs to run it's operations
struct BSQMemoryTheadLocalInfo
{
    size_t tl_id; //ID of the thread

    GCAllocator** g_gcallocs;

    ////
    //Mark Phase information
    void** native_stack_base; //the base of the native stack

    ArrayList<void*> native_stack_contents; //the contents of the native stack extracted in the mark phase
    RegisterContents native_register_contents; //the contents of the native registers extracted in the mark phase

    //We assume that the roots always fit in a single page block
    int32_t roots_count;
    void** roots;
    
    int32_t old_roots_count;
    void** old_roots;

    int forward_table_index;
    void** forward_table;

    uint64_t typeptr_high32; // high 32 bits taken from a typeinfo pointer

    uint32_t newly_filled_pages_count = 0;

    ArrayList<void*> pending_roots; //the worklist of roots that we need to do visits from
    ArrayList<MarkStackEntry> visit_stack; //stack for doing a depth first visit (and topo organization) of the object graph

    ArrayList<void*> pending_young; //the list of young objects that need to be processed
    ArrayList<void*> pending_decs; //the list of objects that need to be decremented 

    //TODO: Once PID is implemented this will need to use this->max_decrement_count
    uint32_t decremented_pages_index = 0;
    PageInfo* decremented_pages[BSQ_INITIAL_MAX_DECREMENT_COUNT];

    size_t max_decrement_count;

    uint8_t g_gcallocs_lookuptable[MAX_ALLOC_LOOKUP_TABLE_SIZE] = {};
    uint8_t g_gcallocs_idx = 0;

    //We may want this in prod, so i'll have it always be visible
    bool disable_automatic_collections = false;

    MemStats mstats;

#ifdef BSQ_GC_CHECK_ENABLED
    bool disable_stack_refs_for_tests = false;
#endif

    BSQMemoryTheadLocalInfo() noexcept : tl_id(0), g_gcallocs(nullptr), native_stack_base(nullptr), native_stack_contents(), native_register_contents(), roots_count(0), roots(nullptr), old_roots_count(0), old_roots(nullptr), forward_table_index(FWD_TABLE_START), forward_table(nullptr), typeptr_high32(0), pending_roots(), visit_stack(), pending_young(), pending_decs(), max_decrement_count(BSQ_INITIAL_MAX_DECREMENT_COUNT), mstats() { }

    inline GCAllocator* getAllocatorForPageSize(PageInfo* page) noexcept {
        uint8_t idx = this->g_gcallocs_lookuptable[page->allocsize >> 3];
        return this->g_gcallocs[idx];
    }

    inline uint8_t generateAllocLookupIndex(GCAllocator* alloc) noexcept 
    {
        size_t idx = alloc->getAllocSize() >> 3;
        if(this->g_gcallocs_lookuptable[idx] == 0) {
            this->g_gcallocs_lookuptable[idx] = this->g_gcallocs_idx++;
        }

        return this->g_gcallocs_lookuptable[idx];
    }

    template <size_t NUM>
    void initializeGC(GCAllocator* allocs[NUM]) noexcept
    {
        for(size_t i = 0; i < NUM; i++) {
            GCAllocator* alloc = allocs[i];
            uint8_t idx = generateAllocLookupIndex(alloc);
            this->g_gcallocs[idx] = alloc;
        }
    }

    void initialize(size_t ntl_id, void** caller_rbp) noexcept;

    void loadNativeRootSet() noexcept;
    void unloadNativeRootSet() noexcept;
};

//
// OOF, this shit breaks my tests as we do not
// calculate total live bytes anymore :(
//
// Lets think about this after a good nights rest!
//
#ifdef MEM_STATS
#include <iostream>

#define BUCKET_VARIANCE 0.05
#define BUCKET_AVERAGE ((BUCKET_VARIANCE) / 2)

#define TOTAL_ALLOC_COUNT(E)      (E).mstats.total_alloc_count
#define TOTAL_ALLOC_MEMORY(E)     (E).mstats.total_alloc_memory
#define TOTAL_COLLECTIONS(E)      (E).mstats.total_collections
#define MIN_COLLECTION_TIME(E)    (E).mstats.min_collection_time
#define MAX_COLLECTION_TIME(E)    (E).mstats.max_collection_time
#define MAX_LIVE_HEAP(E)          (E).mstats.max_live_heap

#define UPDATE_TOTAL_ALLOC_COUNT(E, OP, ...)      TOTAL_ALLOC_COUNT((E)) OP __VA_ARGS__
#define UPDATE_TOTAL_ALLOC_MEMORY(E, OP, ...)     TOTAL_ALLOC_MEMORY((E)) OP __VA_ARGS__
#define UPDATE_TOTAL_COLLECTIONS(E, OP, ...)      TOTAL_COLLECTIONS((E)) OP __VA_ARGS__
#define UPDATE_MIN_COLLECTION_TIME(E, OP, ...)    MIN_COLLECTION_TIME((E)) OP __VA_ARGS__
#define UPDATE_MAX_COLLECTION_TIME(E, OP, ...)    MAX_COLLECTION_TIME((E)) OP __VA_ARGS__
#define UPDATE_MAX_LIVE_HEAP(E, OP, ...)          MAX_LIVE_HEAP((E)) OP __VA_ARGS__

inline void update_bucket(uint64_t* bucket, double time) noexcept 
{
    int index = static_cast<int>((time * (1.0 / BUCKET_VARIANCE)) + 0.5);
    if(index >= MAX_MEMSTATS_BUCKETS) { 
        bucket[MAX_MEMSTATS_BUCKETS - 1]++;
    }
    else {
        bucket[index]++;
    }
}

double compute_average_time(uint64_t buckets[MAX_MEMSTATS_BUCKETS]) noexcept;
std::string generate_formatted_memstats(MemStats& ms) noexcept;

#define PRINT_COLLECTION_TIME(E)                                                                                 \
    do{                                                                                                          \
        std::cout << "Average Collection Time: " << compute_average_time((E).mstats.collection_times) << "ms\n"; \
        std::cout << "Min Collection Time: " << (E).mstats.min_collection_time << "ms\n";                        \
        std::cout << "Max Collection Time: " << (E).mstats.max_collection_time << "ms\n";                        \
    } while(0)

#define PRINT_MARKING_TIME(E) \
    (std::cout << "Average Marking Time: " << compute_average_time((E).mstats.marking_times) << "ms\n")

#define PRINT_EVACUATION_TIME(E) \
    (std::cout << "Average Evacuation Time: " << compute_average_time((E).mstats.evacuation_times) << "ms\n")

#define PRINT_DECREMENT_TIME(E) \
    (std::cout << "Average Decrement Time: " << compute_average_time((E).mstats.decrement_times) << "ms\n")

#define PRINT_TOTAL_COLLECTIONS(E) \
    (std::cout << "Total Collections: " << (E).mstats.total_collections << "\n")

#define PRINT_ALLOC_INFO(E)                                                                     \
    do {                                                                                        \
        std::cout << "Total Alloc Count: " << (E).mstats.total_alloc_count << "\n";             \
        std::cout << "Total Allocated Memory: " << (E).mstats.total_alloc_memory << " bytes\n"; \
    } while(0)

#define PRINT_MAX_HEAP(E) \
    (std::cout << "Max Live Heap Size: " << (E).mstats.max_live_heap << " bytes\n")

#define MEM_STATS_DUMP(E)           \
    do {                            \
        PRINT_COLLECTION_TIME(E);   \
        PRINT_MARKING_TIME(E);      \
        PRINT_EVACUATION_TIME(E);   \
        PRINT_DECREMENT_TIME(E);    \
        PRINT_TOTAL_COLLECTIONS(E); \
        PRINT_ALLOC_INFO(E);        \
        PRINT_MAX_HEAP(E);          \
    } while(0)

#else
#define TOTAL_ALLOC_COUNT(E)      0
#define TOTAL_ALLOC_MEMORY(E)     0
#define TOTAL_COLLECTIONS(E)      0
#define MIN_COLLECTION_TIME(E)    0
#define MAX_COLLECTION_TIME(E)    0
#define MAX_LIVE_HEAP(E)          0

#define UPDATE_TOTAL_ALLOC_COUNT(E, OP, ...)
#define UPDATE_TOTAL_ALLOC_MEMORY(E, OP, ...)
#define UPDATE_TOTAL_COLLECTIONS(E, OP, ...)
#define UPDATE_MIN_COLLECTION_TIME(E, OP, ...)
#define UPDATE_MAX_COLLECTION_TIME(E, OP, ...)
#define UPDATE_MAX_LIVE_HEAP(E, OP, ...)

#define update_bucket (void)sizeof
#define compute_average_time(B) 0
#define generate_formatted_memstats(MS) ""

#define MEM_STATS_DUMP(E)
#endif // MEM_STATS

extern thread_local BSQMemoryTheadLocalInfo gtl_info;