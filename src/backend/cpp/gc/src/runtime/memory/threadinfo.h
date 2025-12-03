#pragma once 

#include "allocator.h"

#include <thread>
#include <condition_variable>
#include <mutex>

#ifdef MEM_STATS
#include <chrono>
#endif

#define InitBSQMemoryTheadLocalInfo() { ALLOC_LOCK_ACQUIRE(); register void** rbp asm("rbp"); gtl_info.initialize(GlobalThreadAllocInfo::s_thread_counter++, rbp); ALLOC_LOCK_RELEASE(); }

#define MAX_ALLOC_LOOKUP_TABLE_SIZE 1024

#define MARK_STACK_NODE_COLOR_GREY 0
#define MARK_STACK_NODE_COLOR_BLACK 1

#define FWD_TABLE_START 1

struct BSQMemoryTheadLocalInfo;

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

// Buckets store BUCKET_VARIANCE ms variance, final entry is for outliers (hopefully never any values present there!)
#define MAX_MEMSTATS_BUCKETS 10000 + 1
struct Stats {
    size_t count = 0;
    double mean  = 0.0;
    double M2    = 0.0;
    double total = 0.0;
};
struct MemStats {
    size_t total_alloc_count  = 0;
    size_t prev_total_alloc_count = 0;
    size_t total_alloc_memory = 0;
    size_t total_live_bytes   = 0;
    size_t total_live_objects = 0;
    size_t total_promotions   = 0;
    size_t total_pages        = 0;

    Stats collection_stats { 0 };
    Stats nursery_stats    { 0 };
    Stats rc_stats         { 0 };

    double start_time = 0.0;
    double total_time = 0.0;

    double survival_rate_sum = 0.0;

    double min_collection_time = 0;
    double max_collection_time = 0;

    size_t max_live_heap = 0;

    size_t collection_times[MAX_MEMSTATS_BUCKETS] { 0 };
    size_t nursery_times[MAX_MEMSTATS_BUCKETS]    { 0 };
    size_t rc_times[MAX_MEMSTATS_BUCKETS]         { 0 };
};
#else
struct MemStats {};
#endif

// An object for processing RC decrements on separate thread
struct DecsProcessor {
    std::condition_variable cv;
    std::mutex mtx;
    std::jthread worker;

    ArrayList<void*> pending;
    void (*processDecfp)(void*, BSQMemoryTheadLocalInfo&);

    bool canrun;
    bool needs_merge;

    DecsProcessor(BSQMemoryTheadLocalInfo* tinfo): cv(), mtx(), worker(&DecsProcessor::process, this, tinfo), pending(), processDecfp(nullptr), canrun(false), needs_merge(false) {
        this->pending.initialize();
    }

    void requestMergeAndPause(std::unique_lock<std::mutex>& lk)
    {
        this->canrun = false;
        this->needs_merge = true;
        this->cv.notify_one();

        // Once canrun is false we know the decs thread ackd our merge request
        cv.wait(lk, [this]{ return !this->canrun; });
    }

    void resumeAfterMerge(std::unique_lock<std::mutex>& lk)
    {
        this->canrun = true;
        this->needs_merge = false;
        lk.unlock();
        this->cv.notify_one();
    }

    void process(BSQMemoryTheadLocalInfo* tinfo)
    {
        while(true) {
            std::unique_lock lk(this->mtx);
            cv.wait(lk, [this]{ 
                return this->canrun && !this->needs_merge; 
            });

            while(!this->pending.isEmpty()) {
                if(this->processDecfp != nullptr) {
                    void* obj = this->pending.pop_front();
                    this->processDecfp(obj, *tinfo);
                }
            }
        }
    }
};

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

    int32_t forward_table_index;
    void** forward_table;

    DecsProcessor decs; 
    ArrayList<void*> decs_batch; // Decrements able to be done without needing decs thread

    // Arbitrary size for now --- fix before merging
    uint32_t decd_pages_idx = 0;
    PageInfo* decd_pages[10'000];
    
    float nursery_usage = 0.0f;

    ArrayList<void*> pending_roots; //the worklist of roots that we need to do visits from
    ArrayList<MarkStackEntry> visit_stack; //stack for doing a depth first visit (and topo organization) of the object graph

    ArrayList<void*> pending_young; //the list of young objects that need to be processed

    size_t max_decrement_count;

    uint8_t g_gcallocs_lookuptable[MAX_ALLOC_LOOKUP_TABLE_SIZE] = {};
    uint8_t g_gcallocs_idx = 0;

    //We may want this in prod, so i'll have it always be visible
    bool disable_automatic_collections = false;

    MemStats mstats;

#ifdef BSQ_GC_CHECK_ENABLED
    bool disable_stack_refs_for_tests = false;
    bool enable_global_rescan         = false;
#endif

    BSQMemoryTheadLocalInfo() noexcept : tl_id(0), g_gcallocs(nullptr), 
        native_stack_base(nullptr), native_stack_contents(), native_register_contents(), 
        roots_count(0), roots(nullptr), old_roots_count(0), old_roots(nullptr), 
        forward_table_index(FWD_TABLE_START), forward_table(nullptr), decs(this), 
        decs_batch(), decd_pages_idx(0), decd_pages(), pending_roots(), visit_stack(), 
        pending_young(), max_decrement_count(BSQ_INITIAL_MAX_DECREMENT_COUNT), mstats() 
    { }
    BSQMemoryTheadLocalInfo& operator=(BSQMemoryTheadLocalInfo&) = delete;
    BSQMemoryTheadLocalInfo(BSQMemoryTheadLocalInfo&) = delete;

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

#ifdef MEM_STATS
        auto start = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double, std::milli> dur = start.time_since_epoch();
        this->mstats.start_time = dur.count();
#endif
    }

    inline void updateNurseryUsage(PageInfo* p) noexcept
    {
        this->nursery_usage += 1.0f - p->approx_utilization;
    }

    void initialize(size_t ntl_id, void** caller_rbp) noexcept;

    void loadNativeRootSet() noexcept;
    void unloadNativeRootSet() noexcept;
};

#ifdef MEM_STATS
#include <iostream>

#define BUCKET_VARIANCE 0.001
#define BUCKET_AVERAGE ((BUCKET_VARIANCE) / 2)

inline void update_bucket(size_t* bucket, double time) noexcept 
{
    int index = static_cast<int>((time * (1.0 / BUCKET_VARIANCE)) + 0.5);
    if(index >= MAX_MEMSTATS_BUCKETS) { 
        bucket[MAX_MEMSTATS_BUCKETS - 1]++;
    }
    else {
        bucket[index]++;
    }
}

void update_stats(Stats& stats, double time) noexcept;
double get_mean_pause(Stats& stats) noexcept;
double get_stddev(const Stats& stats) noexcept;

std::string generate_formatted_memstats(MemStats& ms) noexcept;

inline double calculate_percentile_from_buckets(const size_t* buckets, double percentile) noexcept 
{
    size_t total = 0;
    for (int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        total += buckets[i];
    }
    
    if (total == 0) {
        return 0.0;
    }
    
    size_t target_count = static_cast<size_t>(total * percentile);
    size_t cumulative = 0;
    
    for (int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        cumulative += buckets[i];
        if (cumulative >= target_count) {
            return i * BUCKET_VARIANCE;
        }
    }
    
    return (MAX_MEMSTATS_BUCKETS - 1) * BUCKET_VARIANCE;
}

inline void update_collection_extrema(MemStats& ms, double time) noexcept 
{
    if(time > ms.max_collection_time) { 
        ms.max_collection_time = time;  
    }
    if(time < ms.min_collection_time || ms.min_collection_time < 1e-10) { 
        ms.min_collection_time = time;
    }
}

inline void update_collection_stats(MemStats& ms, double time) noexcept 
{
    update_collection_extrema(ms, time);
    update_stats(ms.collection_stats, time);
}

inline void update_nursery_stats(MemStats& ms, double time) noexcept 
{
    update_stats(ms.nursery_stats, time);
}

inline void update_rc_stats(MemStats& ms, double time) noexcept 
{
    update_stats(ms.rc_stats, time);
}

inline void update_survival_rate_sum(MemStats& ms) noexcept 
{
    ms.survival_rate_sum += static_cast<double>(ms.total_live_objects) / static_cast<double>(ms.total_alloc_count - ms.prev_total_alloc_count);
}

inline double calculate_total_collection_time(const size_t* buckets) noexcept
{
    double curvariance = BUCKET_VARIANCE;
    double total = 0.0;
    for (int i = 0; i < MAX_MEMSTATS_BUCKETS; i++) {
        total += buckets[i] * curvariance;
        curvariance += BUCKET_VARIANCE;
    }

    return total;
}

#define PRINT_COLLECTION_TIME(E) \
    do{ \
        double mean = get_mean_pause((E).mstats.collection_stats); \
        double stddev = get_stddev((E).mstats.collection_stats); \
        std::cout << "Collection Average: " << mean << "ms\n"; \
        std::cout << "Collection Std Dev: " << stddev << "ms\n"; \
        std::cout << "Collection 1σ: " << stddev << "ms\n"; \
        std::cout << "Collection 2σ: " << (2 * stddev) << "ms\n"; \
        std::cout << "Collection Min: " << (E).mstats.min_collection_time << "ms\n"; \
        std::cout << "Collection Max: " << (E).mstats.max_collection_time << "ms\n"; \
        std::cout << "Collection 50th: " << calculate_percentile_from_buckets((E).mstats.collection_times, 0.50) << "ms\n"; \
        std::cout << "Collection 95th: " << calculate_percentile_from_buckets((E).mstats.collection_times, 0.95) << "ms\n"; \
        std::cout << "Collection 99th: " << calculate_percentile_from_buckets((E).mstats.collection_times, 0.99) << "ms\n"; \
    } while(0)
#define PRINT_TOTAL_COLLECTIONS(E) \
    (std::cout << "Total Collections: " << (E).mstats.collection_stats.count << "\n")

#define PRINT_NURSERY_TIME(E) \
        std::cout << "Nursery Average: " << get_mean_pause((E).mstats.nursery_stats) << "ms\n";

#define PRINT_RC_TIME(E) \
    std::cout << "RC Average: " << get_mean_pause((E).mstats.rc_stats) << "ms\n";

#define PRINT_TOTAL_PAGES(E) \
    (std::cout << "Total Pages: " << (E).mstats.total_pages << "\n")

#define PRINT_HEAP_SIZE(E) \
    (std::cout << "Heap Size: " << (E).mstats.total_pages * BSQ_BLOCK_ALLOCATION_SIZE << " bytes\n")

#define PRINT_ALLOC_INFO(E)                                                                     \
    do {                                                                                        \
        std::cout << "Total Alloc Count: " << (E).mstats.total_alloc_count << "\n";             \
        std::cout << "Total Allocated Memory: " << (E).mstats.total_alloc_memory << " bytes\n"; \
    } while(0)

#define PRINT_TOTAL_PROMOTIONS(E) \
    (std::cout << "Total Promotions: " << (E).mstats.total_promotions << "\n")

#define PRINT_MAX_HEAP(E) \
    (std::cout << "Max Live Heap Size: " << (E).mstats.max_live_heap << " bytes\n")

#define PRINT_TOTAL_TIME(E) \
    do {\
        (E).mstats.total_time -= (E).mstats.start_time; \
        std::cout << "Total Time: " << (E).mstats.total_time << "ms\n"; \
        std::cout << "Percentage of Time Collecting: " << (calculate_total_collection_time((E).mstats.collection_times) / (E).mstats.total_time) * 100.0 << "%\n";\
    } while(0)

#define PRINT_SURVIVAL_RATE(E) \
    std::cout << "Survival Rate: " << ((E).mstats.survival_rate_sum / static_cast<double>((E).mstats.collection_stats.count)) * 100.0 << "%\n";

#define MEM_STATS_DUMP(E) \
    do { \
        PRINT_COLLECTION_TIME(E); \
        PRINT_NURSERY_TIME(E); \
        PRINT_RC_TIME(E); \
        PRINT_TOTAL_TIME(E); \
        PRINT_TOTAL_COLLECTIONS(E); \
        PRINT_TOTAL_PROMOTIONS(E); \
        PRINT_ALLOC_INFO(E); \
        PRINT_TOTAL_PAGES(E); \
        PRINT_MAX_HEAP(E); \
        PRINT_HEAP_SIZE(E); \
        PRINT_SURVIVAL_RATE(E); \
    } while(0)

#else
#define update_bucket (void)sizeof
#define compute_average_time(B) 0
#define generate_formatted_memstats(MS) ""

#define MEM_STATS_DUMP(E)
#endif // MEM_STATS

extern thread_local BSQMemoryTheadLocalInfo gtl_info;