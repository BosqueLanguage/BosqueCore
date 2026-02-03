#pragma once 

#include "allocator.h"

#include <chrono>

#define InitBSQMemoryTheadLocalInfo() { std::lock_guard lk(g_alloclock); register void** rbp asm("rbp"); gtl_info.initialize(GlobalThreadAllocInfo::s_thread_counter++, rbp); }

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

    ArrayList<void*> decs_batch; // Decrements able to be done without needing decs thread	
    ArrayList<PageInfo*> decd_pages;
    
    float nursery_usage = 0.0f;

    ArrayList<void*> pending_roots; //the worklist of roots that we need to do visits from
    ArrayList<MarkStackEntry> visit_stack; //stack for doing a depth first visit (and topo organization) of the object graph

    ArrayList<void*> pending_young; //the list of young objects that need to be processed

	size_t bytes_freed; // Number of bytes freed within a collection
    size_t max_decrement_count;

    bool disable_automatic_collections;

#ifdef BSQ_GC_TESTING
    // having thread local storage of root pointers is useful for testing 
	// interactions of multiple threads (ensuring roots are kept alive if 
	// still reachable from at least one thread)
	void* thd_testing_data[NUM_THREAD_TESTING_ROOTS] = { nullptr };
#endif

    BSQMemoryTheadLocalInfo() noexcept : 
        tl_id(0), g_gcallocs(nullptr), native_stack_base(nullptr), native_stack_contents(), 
        native_register_contents(), roots_count(0), roots(nullptr), old_roots_count(0), 
        old_roots(nullptr), forward_table_index(FWD_TABLE_START), forward_table(nullptr), 
        decs_batch(), decd_pages(), nursery_usage(0.0f), pending_roots(), visit_stack(), 
		pending_young(), bytes_freed(0), max_decrement_count(0), 
		disable_automatic_collections(false) { }
    BSQMemoryTheadLocalInfo& operator=(BSQMemoryTheadLocalInfo&) = delete;
    BSQMemoryTheadLocalInfo(BSQMemoryTheadLocalInfo&) = delete;
	~BSQMemoryTheadLocalInfo() { this->cleanup(); }

	inline GCAllocator* getAllocatorForPageSize(PageInfo* page) noexcept {
        uint32_t idx = page->typeinfo->type_id;
 		GC_INVARIANT_CHECK(idx < BSQ_MAX_ALLOC_SLOTS);	       

		return this->g_gcallocs[idx];
    }

    template <size_t NUM>
    void initializeGC(GCAllocator* allocs[NUM]) noexcept
    {
        for(size_t i = 0; i < NUM; i++) {
            GCAllocator* alloc = allocs[i];
            uint32_t idx = alloc->getAllocType()->type_id;
			GC_INVARIANT_CHECK(idx < BSQ_MAX_ALLOC_SLOTS);	

			this->g_gcallocs[idx] = alloc;
        }
    }

    inline void updateNurseryUsage(PageInfo* p) noexcept
    {
        this->nursery_usage += 1.0f - p->approx_utilization;
    }

    void initialize(size_t ntl_id, void** caller_rbp) noexcept;

    void loadNativeRootSet() noexcept;
    void unloadNativeRootSet() noexcept;
	void cleanup() noexcept;
};

extern thread_local BSQMemoryTheadLocalInfo gtl_info;
