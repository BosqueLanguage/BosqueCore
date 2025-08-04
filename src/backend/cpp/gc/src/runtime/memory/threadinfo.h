#pragma once 

#include "allocator.h"

#define InitBSQMemoryTheadLocalInfo() { ALLOC_LOCK_ACQUIRE(); register void** rbp asm("rbp"); gtl_info.initialize(GlobalThreadAllocInfo::s_thread_counter++, rbp); ALLOC_LOCK_RELEASE(); }

#define MAX_MEMSTAT_TIMES_INDEX 512

#define MAX_ALLOC_LOOKUP_TABLE_SIZE 1024

#define MARK_STACK_NODE_COLOR_GREY 0
#define MARK_STACK_NODE_COLOR_BLACK 1

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

    void* rax;
    void* rbx;
    void* rcx;
    void* rdx;
    void* rsi;
    void* rdi;
    void* r8;
    void* r9;
    void* r10;
    void* r11;
    void* r12;
    void* r13;
    void* r14;
    void* r15;
};

//All of the data that a thread local allocator needs to run it's operations
struct BSQMemoryTheadLocalInfo
{
    size_t tl_id; //ID of the thread

    GCAllocator** g_gcallocs;

    ////
    //Mark Phase information
    void** native_stack_base; //the base of the native stack

    size_t native_stack_count;
    void** native_stack_contents; //the contents of the native stack extracted in the mark phase
    RegisterContents native_register_contents; //the contents of the native registers extracted in the mark phase

    //We assume that the roots always fit in a single page block
    size_t roots_count;
    void** roots;
    
    size_t old_roots_count;
    void** old_roots;

    size_t forward_table_index = 0;
    void** forward_table;

    uint32_t newly_filled_pages_count = 0;

    ArrayList<void*> pending_roots; //the worklist of roots that we need to do visits from
    ArrayList<MarkStackEntry> visit_stack; //stack for doing a depth first visit (and topo organization) of the object graph

    ArrayList<void*> pending_young; //the list of young objects that need to be processed
    ArrayList<void*> pending_decs; //the list of objects that need to be decremented 

    //TODO: Once PID is implemented this will need to use this->max_decrement_count
    int decremented_pages_index = 0;
    PageInfo* decremented_pages[BSQ_INITIAL_MAX_DECREMENT_COUNT];

    size_t max_decrement_count;

    uint8_t g_gcallocs_lookuptable[MAX_ALLOC_LOOKUP_TABLE_SIZE] = {};
    uint8_t g_gcallocs_idx = 0;

    //We may want this in prod, so i'll have it always be visible
    bool disable_automatic_collections = false;

#ifdef MEM_STATS
    uint64_t num_allocs = 0;
    uint64_t total_gc_pages = 0;
    uint64_t total_empty_gc_pages = 0;
    uint64_t total_live_bytes = 0; //doesnt include canary or metadata size

    int collection_times_index = 0;
    double collection_times[MAX_MEMSTAT_TIMES_INDEX]; //store in ms how much time each collection takes

    int marking_times_index = 0;
    double marking_times[MAX_MEMSTAT_TIMES_INDEX];

    int evacuation_times_index = 0;
    double evacuation_times[MAX_MEMSTAT_TIMES_INDEX];

    int decrement_times_index = 0;
    double decrement_times[MAX_MEMSTAT_TIMES_INDEX];
#endif

#ifdef BSQ_GC_CHECK_ENABLED
    bool disable_stack_refs_for_tests = false;
#endif

    BSQMemoryTheadLocalInfo() noexcept : tl_id(0), g_gcallocs(nullptr), native_stack_base(nullptr), native_stack_count(0), native_stack_contents(nullptr), roots_count(0), roots(nullptr), old_roots_count(0), old_roots(nullptr), forward_table_index(0), forward_table(nullptr), pending_roots(), visit_stack(), pending_young(), pending_decs(), max_decrement_count(BSQ_INITIAL_MAX_DECREMENT_COUNT) { }

    inline GCAllocator* getAllocatorForPageSize(PageInfo* page) noexcept {
        uint8_t idx = this->g_gcallocs_lookuptable[page->allocsize >> 3];
        GCAllocator* gcalloc = this->g_gcallocs[idx];
        return gcalloc;
    }

    inline uint8_t generateAllocLookupIndex(GCAllocator* alloc) noexcept 
    {
        size_t size = alloc->getAllocSize() >> 3;
        if(this->g_gcallocs_lookuptable[size] == 0) {
            this->g_gcallocs_lookuptable[size] = this->g_gcallocs_idx++;
        }

        return this->g_gcallocs_lookuptable[size];
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

    void initialize(size_t tl_id, void** caller_rbp) noexcept;

    void loadNativeRootSet() noexcept;
    void unloadNativeRootSet() noexcept;
};

#ifdef MEM_STATS
    #define NUM_ALLOCS(E)           (E).num_allocs
    #define TOTAL_GC_PAGES(E)       (E).total_gc_pages
    #define TOTAL_EMPTY_GC_PAGES(E) (E).total_empty_gc_pages
    #define TOTAL_LIVE_BYTES(E)     (E).total_live_bytes

    #define UPDATE_NUM_ALLOCS(E, OP, ...)           NUM_ALLOCS(E) OP __VA_ARGS__
    #define UPDATE_TOTAL_GC_PAGES(E, OP, ...)       TOTAL_GC_PAGES(E) OP __VA_ARGS__
    #define UPDATE_TOTAL_EMPTY_GC_PAGES(E, OP, ...) TOTAL_EMPTY_GC_PAGES(E) OP __VA_ARGS__
    #define UPDATE_TOTAL_LIVE_BYTES(E, OP, ...)     TOTAL_LIVE_BYTES(E) OP __VA_ARGS__

    double compute_average_time(double time[MAX_MEMSTAT_TIMES_INDEX], int size) noexcept;
    
    #define PRINT_COLLECTION_TIME(E) (std::cout << "Average Collection Time: " << compute_average_time((E).collection_times, (E).collection_times_index) << "ms\n")
    #define PRINT_MARKING_TIME(E) (std::cout << "Average Marking Time: " << compute_average_time((E).marking_times, (E).marking_times_index) << "ms\n")
    #define PRINT_EVACUATION_TIME(E) (std::cout << "Average Evacuation Time: " << compute_average_time((E).evacuation_times, (E).evacuation_times_index) << "ms\n")
    #define PRINT_DECREMENT_TIME(E) (std::cout << "Average Decrement Time: " << compute_average_time((E).decrement_times, (E).decrement_times_index) << "ms\n")

    #define MEM_STATS_DUMP(E)     \
    do {                          \
        PRINT_COLLECTION_TIME(E); \
        PRINT_MARKING_TIME(E);    \
        PRINT_EVACUATION_TIME(E); \
        PRINT_DECREMENT_TIME(E);  \
    } while(0)
#else
    #define NUM_ALLOCS(E)           0 
    #define TOTAL_GC_PAGES(E)       0
    #define TOTAL_EMPTY_GC_PAGES(E) 0
    #define TOTAL_LIVE_BYTES(E)     0

    #define UPDATE_NUM_ALLOCS(OP, ...)
    #define UPDATE_TOTAL_GC_PAGES(OP, ...)
    #define UPDATE_TOTAL_EMPTY_GC_PAGES(OP, ...)
    #define UPDATE_TOTAL_LIVE_BYTES(OP, ...)

    #define compute_average_time (void)sizeof
    #define MEM_STATS_DUMP(E)
#endif

extern thread_local BSQMemoryTheadLocalInfo gtl_info;