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

// Allows us to correctly determine pointer offsets
#ifdef ALLOC_DEBUG_CANARY
#define REAL_ENTRY_SIZE(ESIZE) (ALLOC_DEBUG_CANARY_SIZE + ESIZE + sizeof(MetaData) + ALLOC_DEBUG_CANARY_SIZE)
#else
#define REAL_ENTRY_SIZE(ESIZE) (ESIZE + sizeof(MetaData))
#endif

////////////////////////////////
//Memory allocator

class PageList;

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

class PageInfo
{
public:
    FreeListEntry* freelist; //allocate from here until nullptr
   
    // NOTE: as our gc allocators are declared statically, the addresses 
    // of a PageList will not change. However, if PageLists need to be 
    // used elsewhere, extra care will be needed (i.e. stack allocs)
    PageList* owner; // What list are we in (if any)?
    PageInfo* prev;
    PageInfo* next;

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

struct PageIterator {
    PageInfo* current;
    
    PageInfo* operator*()
    { 
        return current; 
    }

    PageIterator& operator++() 
    { 
        current = current->next; 
        return *this; 
    }
    
    bool operator!=(const PageIterator& other) 
    { 
        return current != other.current; 
    }
};

class PageList {
    PageInfo* root;

    static void reset(PageInfo* p) noexcept
    {
        p->owner = nullptr;
        p->prev = p->next = nullptr;
    }

public:
    PageList() noexcept : root(nullptr) {}

    bool empty() const noexcept
    {
        return this->root == nullptr;
    }

    void push(PageInfo* p)
    {
        assert(p->prev == nullptr && p->next == nullptr && p->owner == nullptr);
       
        p->owner = this;
        p->prev = nullptr;
        p->next = this->root;

        if(this->root != nullptr) {
            this->root->prev = p;
        }

        this->root = p;
    }

    PageInfo* pop()
    {
        assert(!this->empty());
        
        PageInfo* p = this->root;
        this->root = this->root->next;
        if(this->root != nullptr) {
            this->root->prev = nullptr;
        }

        reset(p);
        return p;
    }

    void remove(PageInfo* p) 
    {
        assert(p->owner == this);

        if(p->prev != nullptr) {
            p->prev->next = p->next;
        } 
        else {
            this->root = p->next;
        }
        
        if(p->next != nullptr) {
            p->next->prev = p->prev;
        } 

        reset(p);
    }

    PageIterator begin() const noexcept 
    {
        return PageIterator{ this->root };
    }

    PageIterator end() const noexcept 
    {
        return PageIterator{ nullptr };
    }
};

class GlobalPageGCManager
{
private:
    PageList empty_pages;
    PageTable pagetable;

    inline void pagetableInsert(void* addr) noexcept
    {
        return this->pagetable.insert(addr);
    }

public:
    static GlobalPageGCManager g_gc_page_manager;

    GlobalPageGCManager() noexcept : empty_pages(), pagetable() { }

    PageInfo* allocateFreshPage(uint16_t entrysize, uint16_t realsize) noexcept;

    bool pagetableQuery(void* addr) noexcept
    {
        return this->pagetable.query(addr);
    }

    void addNewPage(PageInfo* newPage) noexcept
    {
        GC_MEM_LOCK_ACQUIRE();

        this->empty_pages.push(newPage);
        
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

#define NUM_LOW_UTIL_BUCKETS 12
#define NUM_HIGH_UTIL_BUCKETS 6
#define LOW_UTIL_THRESH 0.60f
#define HIGH_UTIL_THRESH 0.90f
#define BUCKET_UTIL_VARIANCE 0.05f
#define IS_LOW_UTIL(U) (U >= 0.01f && U <= LOW_UTIL_THRESH)
#define IS_HIGH_UTIL(U) (U > LOW_UTIL_THRESH && U <= HIGH_UTIL_THRESH)
#define IS_FULL(U) (U > HIGH_UTIL_THRESH && U <= 1.0f)

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

    PageList pendinggc_pages; // Pages that are pending GC
    PageList filled_pages; // Pages with over 90% utilization (no need for buckets here)
    //completely empty pages go back to the global pool

    PageList low_util_buckets[NUM_LOW_UTIL_BUCKETS]; // Pages with 1-60% utilization (does not hold fully empty)
    PageList high_util_buckets[NUM_HIGH_UTIL_BUCKETS]; // Pages with 61-90% utilization 

#ifdef MEM_STATS
    // These two get zeroed at a collection
    size_t alloc_count;
    size_t alloc_memory;
#else 
#endif
    void (*collectfp)();

    PageInfo* getFreshPageForAllocator() noexcept; 
    PageInfo* getFreshPageForEvacuation() noexcept;

    inline void rotateFullAllocPage()
    {
        this->pendinggc_pages.push(this->alloc_page);
    }

    static int getBucketIndex(PageInfo* p)
    {
        float util = p->approx_utilization;
        int idx = 0;
        if(IS_LOW_UTIL(util)) {
            idx = (util - 0.01f) / BUCKET_UTIL_VARIANCE;
            DSA_INVARIANT_CHECK(idx < NUM_LOW_UTIL_BUCKETS);
        }
        else {
            idx = (util - 0.61f) / BUCKET_UTIL_VARIANCE;
            DSA_INVARIANT_CHECK(idx < NUM_HIGH_UTIL_BUCKETS);
        }

        DSA_INVARIANT_CHECK(idx >= 0);
        return idx;
    }

    bool insertPageInBucket(PageInfo* p) 
    {
        float util = p->approx_utilization;
        if(IS_LOW_UTIL(util)) { 
            int idx = getBucketIndex(p);
            this->low_util_buckets[idx].push(p);
            return true;
        }
        else if(IS_HIGH_UTIL(util)) {
            int idx = getBucketIndex(p);
            this->high_util_buckets[idx].push(p);
            return true;
        }
        else {
            return false;
        }
    }

    PageInfo* getLowestLowUtilPage()
    {
        for(int i = 0; i < NUM_LOW_UTIL_BUCKETS; i++) {
            if(!this->low_util_buckets[i].empty()) {
                PageInfo* p = this->low_util_buckets[i].pop();
                return p;
            }
        }

        return nullptr;
    }

    PageInfo* getLowestHighUtilPage()
    {
        for(int i = 0; i < NUM_HIGH_UTIL_BUCKETS; i++) {
            if(!this->high_util_buckets[i].empty()) {
                PageInfo* p = this->high_util_buckets[i].pop();
                return p;
            }
        }

        return nullptr;
    }

    void removePageFromBucket(PageInfo* p) 
    {
        int idx = getBucketIndex(p);

        if(IS_HIGH_UTIL(p->approx_utilization)) {
            this->high_util_buckets[idx].remove(p);
        }
        else {
            this->low_util_buckets[idx].remove(p);
        }
    }   

public:
#ifdef MEM_STATS
    GCAllocator(uint16_t objsize, uint16_t fullsize, void (*collect)()) noexcept : freelist(nullptr), evacfreelist(nullptr), alloc_page(nullptr), evac_page(nullptr), allocsize(objsize), realsize(fullsize), pendinggc_pages(), filled_pages(), alloc_count(0), alloc_memory(0), collectfp(collect) { }
#else 
    GCAllocator(uint16_t objsize, uint16_t fullsize, void (*collect)()) noexcept : freelist(nullptr), evacfreelist(nullptr), alloc_page(nullptr), evac_page(nullptr), allocsize(objsize), realsize(fullsize), pendinggc_pages(), filled_pages(), collectfp(collect) { }
#endif

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
#endif

    // Pretty sure the decs thread may grab a page for reprocessing
    // BUT the alloc thread happens to have just grabbed it and it now
    // has no owner
    PageInfo* tryRemovePage(PageInfo* p) {
        if(p == alloc_page || p == evac_page || p->owner == &this->pendinggc_pages) {
            return nullptr;
        }
    
        if(p->owner == &this->filled_pages) {
            this->filled_pages.remove(p);
        }
        else {
            this->removePageFromBucket(p);
        }

        return p;
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