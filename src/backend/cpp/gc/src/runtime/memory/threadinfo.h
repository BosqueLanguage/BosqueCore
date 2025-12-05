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

    uint64_t typeptr_high32; // high 32 bits taken from a typeinfo pointer

    float nursery_usage = 0.0f;

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

#ifdef BSQ_GC_CHECK_ENABLED
    bool disable_stack_refs_for_tests = false;
    bool enable_global_rescan         = false;
#endif

    BSQMemoryTheadLocalInfo() noexcept : tl_id(0), g_gcallocs(nullptr), native_stack_base(nullptr), native_stack_contents(), native_register_contents(), roots_count(0), roots(nullptr), old_roots_count(0), old_roots(nullptr), forward_table_index(FWD_TABLE_START), forward_table(nullptr), typeptr_high32(0), pending_roots(), visit_stack(), pending_young(), pending_decs(), max_decrement_count(BSQ_INITIAL_MAX_DECREMENT_COUNT) { }

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

extern thread_local BSQMemoryTheadLocalInfo gtl_info;