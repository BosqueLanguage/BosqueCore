#pragma once 

#include "../common.h"
#include "allocator.h"

#include <chrono>

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
	void (*collectfp)();

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

    ArrayList<void*> decs_batch; // Decrements able to be done without needing decs thread	
    PageList decd_pages; // pages with newly decd (and now dead) objects
    
    float nursery_usage = 0.0f;

    ArrayList<void*> pending_roots; //the worklist of roots that we need to do visits from
    ArrayList<MarkStackEntry> visit_stack; //stack for doing a depth first visit (and topo organization) of the object graph

    ArrayList<void*> pending_young; //the list of young objects that need to be processed

    size_t max_decrement_count;

    bool disable_automatic_collections;
	bool disable_stack_refs = false;
#ifdef MEM_STATS
	MemStats memstats;
#endif

#ifdef BSQ_GC_TESTING
    // having thread local storage of root pointers is useful for testing 
	// interactions of multiple threads (ensuring roots are kept alive if 
	// still reachable from at least one thread)
	void* thd_testing_data[NUM_THREAD_TESTING_ROOTS];
	bool thd_testing = true;
#endif

#ifndef MEM_STATS
    BSQMemoryTheadLocalInfo() noexcept : 
        tl_id(0), g_gcallocs(nullptr), collectfp(nullptr), native_stack_base(nullptr), native_stack_contents(), 
        native_register_contents(), roots_count(0), roots(nullptr), old_roots_count(0), 
        old_roots(nullptr), forward_table_index(FWD_TABLE_START), forward_table(nullptr), 
        decs_batch(), decd_pages(), nursery_usage(0.0f), pending_roots(), visit_stack(), 
		pending_young(), max_decrement_count(BSQ_INITIAL_MAX_DECREMENT_COUNT), 
		disable_automatic_collections(false) {}
#else
    BSQMemoryTheadLocalInfo() noexcept : 
        tl_id(0), g_gcallocs(nullptr), collectfp(nullptr), native_stack_base(nullptr), native_stack_contents(), 
        native_register_contents(), roots_count(0), roots(nullptr), old_roots_count(0), 
        old_roots(nullptr), forward_table_index(FWD_TABLE_START), forward_table(nullptr), 
        decs_batch(), decd_pages(), nursery_usage(0.0f), pending_roots(), visit_stack(), 
		pending_young(), max_decrement_count(BSQ_INITIAL_MAX_DECREMENT_COUNT), 
		disable_automatic_collections(false), memstats() {}
#endif
	BSQMemoryTheadLocalInfo& operator=(BSQMemoryTheadLocalInfo&) = delete;
    BSQMemoryTheadLocalInfo(BSQMemoryTheadLocalInfo&) = delete;
	~BSQMemoryTheadLocalInfo() { this->cleanup(); }

    inline void updateNurseryUsage(PageInfo* p) noexcept
    {
        this->nursery_usage += 1.0f - p->approx_utilization;
    }

#ifdef BSQ_GC_TESTING
	template <size_t N>
	void insertThreadTestData(void* testroots[N]) noexcept
	{
		static_assert(N < static_cast<size_t>(NUM_THREAD_TESTING_ROOTS));   
		for(size_t i = 0; i < N; i++) {
			this->thd_testing_data[i] = testroots[i];
		}
	}

	constexpr void clearThreadTestData() noexcept
	{
		for(unsigned i = 0; i < NUM_THREAD_TESTING_ROOTS; i++) {
			this->thd_testing_data[i] = nullptr; 
		}
	}
#endif
	void initialize(size_t ntl_id, void** caller_rbp, void (*_collectfp)()) noexcept;
	void initializeGC(GCAllocator** allocs, size_t n, bool _disable_stack_refs
		, void (*_collectfp)()) noexcept;
	void loadNativeRootSet() noexcept;
    void unloadNativeRootSet() noexcept;
	void updateGlobalMemstats();	
	void cleanup() noexcept;
};

extern thread_local BSQMemoryTheadLocalInfo gtl_info;
