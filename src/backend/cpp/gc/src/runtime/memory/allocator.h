#pragma once

#include "../common.h"
#include "../support/arraylist.h"
#include "../support/pagetable.h"
#include "gc.h"

#ifdef EPSILON
    #include "../support/epsilon.h"
#endif

//Can also use other values like 0xFFFFFFFFFFFFFFFFul
#define ALLOC_DEBUG_MEM_INITIALIZE_VALUE 0x0ul

//Must be multiple of 8
#define ALLOC_DEBUG_CANARY_SIZE 16
#define ALLOC_DEBUG_CANARY_VALUE 0xDEADBEEFDEADBEEFul

#ifdef MEM_STATS
#define MEM_STATS_START(NAME) \
    auto start_##NAME = std::chrono::high_resolution_clock::now()

#define MEM_STATS_END(INFO, BUCKETS, NAME) \
    auto end_##NAME = std::chrono::high_resolution_clock::now(); \
    double NAME##_ms = std::chrono::duration_cast<std::chrono::duration<double, std::milli>>(end_##NAME - start_##NAME).count(); \
    update_bucket((INFO).mstats. BUCKETS, NAME##_ms);

#ifdef COLLECTION_STATS_MODE

#define COLLECTION_STATS_START() \
    MEM_STATS_START(collection)
#define COLLECTION_STATS_END(INFO, BUCKETS) \
    MEM_STATS_END(INFO, BUCKETS, collection)

#define UPDATE_COLLECTION_TIMES(INFO) \
    update_collection_stats((INFO).mstats, collection_ms)

#define NURSERY_STATS_START()
#define NURSERY_STATS_END(INFO, BUCKETS)
#define RC_STATS_START()

#define RC_STATS_END(INFO, BUCKETS)
#define UPDATE_NURSERY_TIMES(INFO) 

#define UPDATE_RC_TIMES(INFO)

#elif defined(NURSERY_RC_STATS_MODE) 

#define UPDATE_COLLECTION_TIMES(INFO)
#define COLLECTION_STATS_START()
#define COLLECTION_STATS_END(INFO, BUCKETS)

#define NURSERY_STATS_START() \
    MEM_STATS_START(nursery)
#define NURSERY_STATS_END(INFO, BUCKETS) \
    MEM_STATS_END(INFO, BUCKETS, nursery)

    #define RC_STATS_START() \
    MEM_STATS_START(rc)
#define RC_STATS_END(INFO, BUCKETS) \
    MEM_STATS_END(INFO, BUCKETS, rc)

#define UPDATE_NURSERY_TIMES(INFO) \
    update_nursery_stats((INFO).mstats, nursery_ms)
#define UPDATE_RC_TIMES(INFO) \
    update_rc_stats((INFO).mstats, rc_ms)
#else
#define UPDATE_COLLECTION_TIMES(INFO)
#define UPDATE_NURSERY_TIMES(INFO)
#define UPDATE_RC_TIMES(INFO)
#endif

#define UPDATE_MEMSTATS_TOTALS(INFO) \
    auto now = std::chrono::high_resolution_clock::now(); \
    gtl_info.mstats.total_time = std::chrono:: \
        duration_cast<std::chrono::duration<double, std::milli>> \
        (now.time_since_epoch()).count(); \
    do { \
        for(size_t i = 0; i < BSQ_MAX_ALLOC_SLOTS; i++) { \
            GCAllocator* alloc = (INFO).g_gcallocs[i]; \
            if(alloc != nullptr) { \
                alloc->updateMemStats(); \
            } \
        } \
    } while(0)

#else
#define MEM_STATS_START(NAME)
#define MEM_STATS_END(INFO, BUCKETS, NAME)

#define COLLECTION_STATS_START()
#define COLLECTION_STATS_END(INFO, BUCKETS)

#define NURSERY_STATS_START()
#define NURSERY_STATS_END(INFO, BUCKETS)

#define RC_STATS_START()
#define RC_STATS_END(INFO, BUCKETS)

#define UPDATE_COLLECTION_TIMES(INFO)
#define UPDATE_NURSERY_TIMES(INFO)
#define UPDATE_RC_TIMES(INFO)
#define UPDATE_MEMSTATS_TOTALS(INFO)
#endif // MEM_STATS

// Allows us to correctly determine pointer offsets
#ifdef ALLOC_DEBUG_CANARY
#define REAL_ENTRY_SIZE(ESIZE) (ALLOC_DEBUG_CANARY_SIZE + ESIZE + sizeof(MetaData) + ALLOC_DEBUG_CANARY_SIZE)
#else
#define REAL_ENTRY_SIZE(ESIZE) (ESIZE + sizeof(MetaData))
#endif

////////////////////////////////
//Memory allocator

//global storage for constant data (and testing support)
//  -- Only a single thread may run while initializing the global roots as they are visible to all threads
//  -- After initialization a GC must be run to promote all values to old ref-count space
//  -- TODO: when we add multi-threading we need to use the special root-ref tag for these roots as well -- then we can skip re-scanning these after the promotion collection

class GlobalDataStorage
{
public:
    void** native_global_storage = nullptr;
    void** native_global_storage_end = nullptr;
    bool needs_scanning = false;

    GlobalDataStorage() noexcept = default;

    static GlobalDataStorage g_global_data;

    void initialize(size_t numbytes, void** data) noexcept
    {
        this->native_global_storage = data;
        this->native_global_storage_end = (void**)((uint8_t*)data + numbytes);

        this->needs_scanning = true;
    }
};

struct FreeListEntry
{
   FreeListEntry* next;
};
static_assert(sizeof(FreeListEntry) <= sizeof(MetaData), "BlockHeader size is not 8 bytes");

#define PAGE_OFFSET_MASK 0xFFF

class PageInfo
{
public:
    FreeListEntry* freelist; //allocate from here until nullptr
    PageInfo* next;
    PageInfo* left; //left pointer in bst
    PageInfo* right; //right pointer in bst

    uint8_t* data; //start of the data block

    uint16_t allocsize; //size of the alloc entries in this page (excluding metadata)
    uint16_t realsize; //size of the alloc entries in this page (including metadata and other stuff)
    
    uint16_t entrycount; //max number of objects that can be allocated from this Page
    uint16_t freecount;

    float approx_utilization;
    uint16_t pending_decs_count;
    bool seen; // Have we visited this page while processing decrements?

    static PageInfo* initialize(void* block, uint16_t allocsize, uint16_t realsize) noexcept;

    void rebuild() noexcept;

    static inline PageInfo* extractPageFromPointer(void* p) noexcept {
        return (PageInfo*)((uintptr_t)(p) & PAGE_ADDR_MASK);
    }

    static inline size_t getIndexForObjectInPage(void* p) noexcept {
        const PageInfo* page = extractPageFromPointer(p);
        
        return (size_t)((uint8_t*)p - page->data) / (size_t)page->realsize;
    }

    static inline MetaData* getObjectMetadataAligned(void* p) noexcept {
        const PageInfo* page = extractPageFromPointer(p);
        size_t idx = (size_t)((uint8_t*)p - page->data) / (size_t)page->realsize;

#ifdef ALLOC_DEBUG_CANARY
        return (MetaData*)(page->data + idx * page->realsize + ALLOC_DEBUG_CANARY_SIZE);
#else
        return (MetaData*)(page->data + idx * page->realsize);
#endif
    }

    inline MetaData* getMetaEntryAtIndex(size_t idx) const noexcept {
#ifdef ALLOC_DEBUG_CANARY
        return (MetaData*)(this->data + idx * this->realsize + ALLOC_DEBUG_CANARY_SIZE);
#else
        return (MetaData*)(this->data + idx * this->realsize);
#endif
    }

    inline void* getObjectAtIndex(size_t idx) const noexcept {
#ifdef ALLOC_DEBUG_CANARY
        return reinterpret_cast<void*>(this->data + idx * this->realsize + ALLOC_DEBUG_CANARY_SIZE + sizeof(MetaData));
#else
        return reinterpret_cast<void*>(this->data + idx * this->realsize + sizeof(MetaData));
#endif
    }

    inline FreeListEntry* getFreelistEntryAtIndex(size_t idx) const noexcept {
        return (FreeListEntry*)(this->data + idx * this->realsize);
    }

    static void initializeWithDebugInfo(void* mem, __CoreGC::TypeInfoBase* type) noexcept
    {
        uint64_t* pre = (uint64_t*)mem;
        *pre = ALLOC_DEBUG_CANARY_VALUE;

        uint64_t* post = (uint64_t*)((uint8_t*)mem + ALLOC_DEBUG_CANARY_SIZE + sizeof(MetaData) + type->type_size);
        *post = ALLOC_DEBUG_CANARY_VALUE;
    }

    inline void decrementPendingDecs() noexcept 
    {
        GC_INVARIANT_CHECK(this->pending_decs_count > 0);
        this->pending_decs_count--;
    }
};

class GlobalPageGCManager
{
private:
    PageInfo* empty_pages;
    PageTable pagetable;

    inline void pagetableInsert(void* addr) noexcept
    {
        return this->pagetable.insert(addr);
    }

public:
    static GlobalPageGCManager g_gc_page_manager;

    GlobalPageGCManager() noexcept : empty_pages(nullptr), pagetable() { }

    PageInfo* allocateFreshPage(uint16_t entrysize, uint16_t realsize) noexcept;

    bool pagetableQuery(void* addr) noexcept
    {
        return this->pagetable.query(addr);
    }

    void addNewPage(PageInfo* newPage) noexcept
    {
        GC_MEM_LOCK_ACQUIRE();

        newPage->next = empty_pages;  
        empty_pages = newPage;    
        
        GC_MEM_LOCK_RELEASE();
    }
};

#ifndef ALLOC_DEBUG_CANARY
#define SETUP_ALLOC_LAYOUT_GET_META_PTR(BASEALLOC) (MetaData*)((uint8_t*)(BASEALLOC))
#define SETUP_ALLOC_LAYOUT_GET_OBJ_PTR(BASEALLOC) (void*)((uint8_t*)(BASEALLOC) + sizeof(MetaData))

#define SET_ALLOC_LAYOUT_HANDLE_CANARY(BASEALLOC, T)
#else
#define SETUP_ALLOC_LAYOUT_GET_META_PTR(BASEALLOC) (MetaData*)((uint8_t*)(BASEALLOC) + ALLOC_DEBUG_CANARY_SIZE)
#define SETUP_ALLOC_LAYOUT_GET_OBJ_PTR(BASEALLOC) (void*)((uint8_t*)(BASEALLOC) + ALLOC_DEBUG_CANARY_SIZE + sizeof(MetaData))

#define SET_ALLOC_LAYOUT_HANDLE_CANARY(BASEALLOC, T) PageInfo::initializeWithDebugInfo(BASEALLOC, T)
#endif

#ifdef VERBOSE_HEADER
#define SETUP_ALLOC_INITIALIZE_FRESH_META(META, T) (*(META)) = { .type=(T), .isalloc=true, .isyoung=true, .ismarked=false, .isroot=false, .forward_index=NON_FORWARDED, .ref_count=0 }
#define SETUP_ALLOC_INITIALIZE_CONVERT_OLD_META(META, T) (*(META)) = { .type=(T), .isalloc=true, .isyoung=false, .ismarked=false, .isroot=false, .forward_index=NON_FORWARDED, .ref_count=0 }
#else
#define SETUP_ALLOC_INITIALIZE_FRESH_META(META, T)       { ZERO_METADATA(META); SET_TYPE_PTR(META, T); (META)->bits.isalloc = 1; (META)->bits.isyoung = 1; } 
#define SETUP_ALLOC_INITIALIZE_CONVERT_OLD_META(META, T) { ZERO_METADATA(META); SET_TYPE_PTR(META, T); (META)->bits.isalloc = 1; (META)->bits.isyoung = 0; }
#endif

template<typename T>
T* MEM_ALLOC_CHECK(T* alloc)
{
    if(alloc == nullptr) {
        assert(false);
    }
    return alloc;
}

#ifdef EPSILON
#define GC_ALLOC_OBJECT(A, L) MEM_ALLOC_CHECK(EpsilonAllocator::alloc.allocate((L)))
#else 
#define GC_ALLOC_OBJECT(A, L) MEM_ALLOC_CHECK((A).allocate((L)))
#endif

#define 𝐀𝐥𝐥𝐨𝐜𝐓𝐲𝐩𝐞(T, A, L, ...) (allocTypeImpl<T>(A, L, __VA_ARGS__))

#define CALC_APPROX_UTILIZATION(P) 1.0f - ((float)P->freecount / (float)P->entrycount)

#define NUM_LOW_UTIL_BUCKETS 12
#define NUM_HIGH_UTIL_BUCKETS 6


#ifdef MEM_STATS
#define UPDATE_ALLOC_STATS(ALLOC, MEMORY_SIZE) \
    (ALLOC)->updateAllocInfo(MEMORY_SIZE)
    
#define RESET_ALLOC_STATS(ALLOC)   \
    do {                           \
        (ALLOC)->alloc_count = 0;  \
        (ALLOC)->alloc_memory = 0; \
    } while(0)

#define GET_ALLOC_COUNT(ALLOC)  ((ALLOC)->alloc_count)
#define GET_ALLOC_MEMORY(ALLOC) ((ALLOC)->alloc_memory)

#else
#define UPDATE_ALLOC_STATS(ALLOC, MEMORY_SIZE)
#define RESET_ALLOC_STATS(ALLOC)
#define GET_ALLOC_COUNT(ALLOC) (0)
#define GET_ALLOC_MEMORY(ALLOC) (0)
#endif

class GCAllocator
{
private:
    FreeListEntry* freelist;
    FreeListEntry* evacfreelist;

    PageInfo* alloc_page; // Page in which we are currently allocating from
    PageInfo* evac_page; // Page in which we are currently evacuating from

    //should match sizes in the page infos
    uint16_t allocsize; //size of the alloc entries in this page (excluding metadata)
    uint16_t realsize;  //size of the alloc entries in this page (including metadata and other stuff)

    PageInfo* pendinggc_pages; // Pages that are pending GC
    PageInfo* filled_pages; // Pages with over 90% utilization (no need for buckets here)
    //completely empty pages go back to the global pool

#ifdef MEM_STATS
    // These two get zeroed at a collection
    size_t alloc_count;
    size_t alloc_memory;
#else 
#endif

    void (*collectfp)();

    PageInfo* getFreshPageForAllocator() noexcept; 
    PageInfo* getFreshPageForEvacuation() noexcept;

public:
#ifdef MEM_STATS
    GCAllocator(uint16_t objsize, uint16_t fullsize, void (*collect)()) noexcept : freelist(nullptr), evacfreelist(nullptr), alloc_page(nullptr), evac_page(nullptr), allocsize(objsize), realsize(fullsize), pendinggc_pages(nullptr), filled_pages(nullptr), alloc_count(0), alloc_memory(0), collectfp(collect) {
        resetBuckets();
    }
#else 
    GCAllocator(uint16_t objsize, uint16_t fullsize, void (*collect)()) noexcept : freelist(nullptr), evacfreelist(nullptr), alloc_page(nullptr), evac_page(nullptr), allocsize(objsize), realsize(fullsize), pendinggc_pages(nullptr), filled_pages(nullptr), collectfp(collect) {
        resetBuckets();
    }
#endif

    // Each "bucket" is a binary tree storing 5% of variance in approx_utiliation
    PageInfo* low_util_buckets[NUM_LOW_UTIL_BUCKETS]; // Pages with 1-60% utilization (does not hold fully empty)
    PageInfo* high_util_buckets[NUM_HIGH_UTIL_BUCKETS]; // Pages with 61-90% utilization 

    inline size_t getAllocSize() const noexcept
    {
        return this->allocsize;
    }

#ifdef MEM_STATS
    inline void updateAllocInfo(uint32_t memory) noexcept
    {
        this->alloc_count++;
        this->alloc_memory += static_cast<size_t>(memory);
    }
#else 
#endif

    inline void resetBuckets() noexcept 
    {
        xmem_zerofill(this->low_util_buckets, NUM_LOW_UTIL_BUCKETS);
        xmem_zerofill(this->high_util_buckets, NUM_HIGH_UTIL_BUCKETS);
    }

    //
    // NOTE: This search is quite slow, if we have a lot of pages
    // maybe problematic (faster that just rebuilding all filled pages though)
    //

    // Remove for reprocessing, called if decrements occured on p
    PageInfo* tryRemoveFromFilledPages(PageInfo* p) {
        if(p == alloc_page || p == evac_page) {
            return nullptr;
        }
    
        PageInfo* prev = nullptr;
        PageInfo* cur = this->filled_pages;
        while(cur != nullptr) {
            if(cur == p) {
                if(prev == nullptr) {
                    this->filled_pages = cur->next;
                }
                else {
                    prev->next = cur->next;
                }
                cur->next = nullptr;
                return p;
            }
            prev = cur;
            cur = cur->next;
        }
        return nullptr;
    }

    inline void* allocate(__CoreGC::TypeInfoBase* type)
    {
        assert(type->type_size == this->allocsize);

        if(this->freelist == nullptr) [[unlikely]] { 
            this->allocatorRefreshAllocationPage(type);
        }
        
        void* entry = this->freelist;
        this->freelist = this->freelist->next;
        
        SET_ALLOC_LAYOUT_HANDLE_CANARY(entry, type);
        SETUP_ALLOC_INITIALIZE_FRESH_META(SETUP_ALLOC_LAYOUT_GET_META_PTR(entry), type);

        UPDATE_ALLOC_STATS(this, type->type_size);

        return SETUP_ALLOC_LAYOUT_GET_OBJ_PTR(entry);
    }

    inline void* allocateEvacuation(__CoreGC::TypeInfoBase* type)
    {
        assert(type->type_size == this->allocsize);

        if(this->evacfreelist == nullptr) [[unlikely]] {
            this->allocatorRefreshEvacuationPage();
        }

        void* entry = this->evacfreelist;
        this->evacfreelist = this->evacfreelist->next;

        SET_ALLOC_LAYOUT_HANDLE_CANARY(entry, type);
        SETUP_ALLOC_INITIALIZE_CONVERT_OLD_META(SETUP_ALLOC_LAYOUT_GET_META_PTR(entry), type);

        return SETUP_ALLOC_LAYOUT_GET_OBJ_PTR(entry);
    }

#ifdef MEM_STATS
    void updateMemStats() noexcept;
#else 
    inline void updateMemStats() noexcept {};
#endif

    //Take a page (that may be in of the page sets -- or may not -- if it is a alloc or evac page) and move it to the appropriate page set
    void processPage(PageInfo* p) noexcept;

    //process all the pending gc pages, the current alloc page, and evac page -- reset for next round
    void processCollectorPages() noexcept;

    //May call collection, insert full alloc page in pending gc pages, get new page
    //To avoid clogging up fast path allocation we initialize high32_typeptr here if needed
    void allocatorRefreshAllocationPage(__CoreGC::TypeInfoBase* typeinfo) noexcept;

    //Get new page for evacuation, append old to filled pages
    void allocatorRefreshEvacuationPage() noexcept;
};

template<typename T, typename... Args>
inline T* allocTypeImpl(GCAllocator& alloc, __CoreGC::TypeInfoBase* typeinfo, Args... args) 
{
    return new (GC_ALLOC_OBJECT(alloc, typeinfo)) T(args...);
}