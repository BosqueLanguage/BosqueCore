#pragma once

#include "../common.h"
#include "../support/arraylist.h"
#include "../support/pagetable.h"
#include "gc.h"

//Can also use other values like 0xFFFFFFFFFFFFFFFFul
#define ALLOC_DEBUG_MEM_INITIALIZE_VALUE 0x0ul

//Must be multiple of 8
#define ALLOC_DEBUG_CANARY_SIZE 16
#define ALLOC_DEBUG_CANARY_VALUE 0xDEADBEEFDEADBEEFul

#ifdef MEM_STATS
#define ENABLE_MEM_STATS
#define MEM_STATS_OP(X) X
#define MEM_STATS_ARG(X) X
#else
#define MEM_STATS_OP(X)
#define MEM_STATS_ARG(X)
#endif

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
    void** native_global_storage;
    void** native_global_storage_end;

    GlobalDataStorage() noexcept : native_global_storage(nullptr), native_global_storage_end(nullptr) { }

    static GlobalDataStorage g_global_data;

    void initialize(size_t numbytes, void** data) noexcept
    {
        this->native_global_storage = data;
        this->native_global_storage_end = (void**)((uint8_t*)data + numbytes);
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

    inline FreeListEntry* getFreelistEntryAtIndex(size_t idx) const noexcept {
        return (FreeListEntry*)(this->data + idx * this->realsize);
    }

    static void initializeWithDebugInfo(void* mem, TypeInfoBase* type) noexcept
    {
        uint64_t* pre = (uint64_t*)mem;
        *pre = ALLOC_DEBUG_CANARY_VALUE;

        uint64_t* post = (uint64_t*)((uint8_t*)mem + ALLOC_DEBUG_CANARY_SIZE + sizeof(MetaData) + type->type_size);
        *post = ALLOC_DEBUG_CANARY_VALUE;
    }
};

class GlobalPageGCManager
{
private:
    PageInfo* empty_pages;
    PageTableInUseInfo pagetable;

public:
    static GlobalPageGCManager g_gc_page_manager;

    GlobalPageGCManager() noexcept : empty_pages(nullptr) { }

    PageInfo* allocateFreshPage(uint16_t entrysize, uint16_t realsize) noexcept;

    bool pagetable_query(void* addr) const noexcept
    {
        return this->pagetable.pagetable_query(addr);
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

#define SETUP_ALLOC_INITIALIZE_FRESH_META(META, T) *(META) = { .type=(T), .isalloc=true, .isyoung=true, .ismarked=false, .isroot=false, .forward_index=MAX_FWD_INDEX, .ref_count=0 }
#define SETUP_ALLOC_INITIALIZE_CONVERT_OLD_META(META, T) *(META) = { .type=(T), .isalloc=true, .isyoung=false, .ismarked=false, .isroot=false, .forward_index=MAX_FWD_INDEX, .ref_count=0 }

#define AllocType(T, A, L) (T*)(A.allocate(L))

#define CALC_APPROX_UTILIZATION(P) 1.0f - ((float)P->freecount / (float)P->entrycount)

#define NUM_LOW_UTIL_BUCKETS 12
#define NUM_HIGH_UTIL_BUCKETS 6

#define IS_LOW_UTIL(U) (U >= 0.01f && U <= 0.60f)
#define IS_HIGH_UTIL(U) (U > 0.60f && U <= 0.90f)

//<=1.0f is very crucial here because new pages start at 100.0f, wihout we just reprocess them until OOM
#define IS_FULL(U) (U > 0.90f && U <= 1.0f)

#define UTILIZATIONS_ARE_EQUAL(F1, F2) (-0.00001 <= (F1 - F2) && (F1 - F2) <= 0.00001)

//Find proper bucket based on increments of 0.05f
#define GET_BUCKET_INDEX(U, N, I, O)                \
do {                                                \
    float tmp_util = 0.0f;                          \
    if(O) {                                         \
        tmp_util = 0.60f;                           \
    }                                               \
    for (int i = 0; i < N; i++) {                   \
        float new_tmp_util = tmp_util + 0.05f;      \
        if (U > tmp_util && U <= new_tmp_util) {    \
            I = i;                                  \
            break;                                  \
        }                                           \
        tmp_util = new_tmp_util;                    \
    }                                               \
} while (0)

class GCAllocator
{
private:
    FreeListEntry* freelist;
    FreeListEntry* evacfreelist;

    PageInfo* alloc_page; // Page in which we are currently allocating from
    PageInfo* evac_page; // Page in which we are currently evacuating from

    //should match sizes in the page infos
    uint16_t allocsize; //size of the alloc entries in this page (excluding metadata)
    uint16_t realsize; //size of the alloc entries in this page (including metadata and other stuff)

    PageInfo* pendinggc_pages; // Pages that are pending GC

    // Each "bucket" is a binary tree storing 5% of variance in approx_utiliation
    PageInfo* low_utilization_buckets[NUM_LOW_UTIL_BUCKETS]; // Pages with 1-60% utilization (does not hold fully empty)
    PageInfo* high_utilization_buckets[NUM_HIGH_UTIL_BUCKETS]; // Pages with 61-90% utilization 

    PageInfo* filled_pages; // Pages with over 90% utilization (no need for buckets here)
    //completely empty pages go back to the global pool

    void (*collectfp)();

    void insertPageInBucket(PageInfo** bucket, PageInfo* new_page, float n_util) 
    {                             
        if(new_page == nullptr) { //sanity check
            assert(false);
        }
        
        PageInfo* root = *bucket;     
        new_page->left = nullptr;
        new_page->right = nullptr;
        new_page->next = nullptr;

        //no root case
        if(root == nullptr) {
            *bucket = new_page;
            return ;
        }
    
        PageInfo* current = root;
        while (current != nullptr) {
            // If current and our pages utilization are equal we add it to this pages list
            // TODO: Insert at beginning of list, means we need a reference from parent node
            if(UTILIZATIONS_ARE_EQUAL(n_util, root->approx_utilization)) {
                if(current->next == nullptr) {
                    current->next = new_page;
                }
                else {
                    PageInfo* it = current;
                    while(it->next != nullptr) {
                        it = it->next;
                    }
                    it->next = new_page;
                }
                break;
            }

            // Traverse down left subtree
            else if (n_util < current->approx_utilization) {
                if (current->left == nullptr) {
                    // Insert as the left child
                    current->left = new_page;
                    break;
                } else {
                    current = current->left;
                }
            } 

            // Traverse down right subtree
            else {
                if (current->right == nullptr) {
                    // Insert as the right child
                    current->right = new_page;
                    break;
                } else {
                    current = current->right;
                }
            }
        }
    }

    void deletePageFromBucket(PageInfo** root_ptr, PageInfo* old_page)
    {
        float old_util = old_page->approx_utilization;
        PageInfo* root = *root_ptr;
        if (root == nullptr) {
            return; 
        }
    
        if (UTILIZATIONS_ARE_EQUAL(old_util, root->approx_utilization)) {
            // Handle case where root itself is the node to delete
            if(root == old_page) {
                if(root->next != nullptr) {
                    *root_ptr = root->next;
                    root->next->left = root->left;  // Preserve left subtree
                    root->next->right = root->right; // Preserve right subtree
                } 
                else {
                    // Normal BST deletion
                    if (root->left == nullptr) {
                        *root_ptr = root->right; 
                    }
                    else if (root->right == nullptr) {
                        *root_ptr = root->left; 
                    }
                    else {
                        PageInfo* successor = getSuccessor(root);

                        // Crucial to update sucessors ptrs
                        successor->left = root->left;
                        successor->right = root->right;
                        successor->next = root->next;

                        root->approx_utilization = successor->approx_utilization;
                        deletePageFromBucket(&root->right, successor);
                    }
                }
                return;
            }
    
            //Handle node in the linked list
            PageInfo* prev = root;
            PageInfo* current = root->next;
            while(current != nullptr) {
                if(current == old_page) {
                    prev->next = current->next;
                    return;
                }
                prev = current;
                current = current->next;
            }
            return; //Node not found
        }

        else if (root->approx_utilization > old_util) {  
            deletePageFromBucket(&((*root_ptr)->left), old_page);
        }
        else {
            deletePageFromBucket(&((*root_ptr)->right), old_page);
        }
    }

    inline PageInfo* getSuccessor(PageInfo* p) 
    {
        p = p->right;
        while(p != nullptr && p->left != nullptr) {
            p = p->left;
        }
        return p;
    }

    PageInfo* findLowestUtilPage(PageInfo** buckets, int n)
    {
        for(int i = 0; i < n; i++) {
            PageInfo* parent = nullptr;
            PageInfo* cur = buckets[i];
            if(cur == nullptr) continue;
            
            while(cur->left != nullptr) {
                parent = cur;
                cur = cur->left;
            }
            
            if(cur == buckets[i]) { // If cur is root
                if(cur->next != nullptr) {
                    buckets[i] = cur->next;
                    buckets[i]->left = cur->left;
                    buckets[i]->right = cur->right;
                } 
                else {
                    // Normal BST removal
                    if(cur->right != nullptr) {
                        buckets[i] = cur->right;
                    } 
                    else {
                        buckets[i] = nullptr;
                    }
                }
            } 
            else { // If cur is not root
                if(cur->right != nullptr) {
                    parent->left = cur->right;
                }
                else {
                    parent->left = nullptr;
                }
            }
            
            return cur;
        }
        return nullptr;
    }

    PageInfo* getFreshPageForAllocator() noexcept
    {
        PageInfo* page = findLowestUtilPage(low_utilization_buckets, NUM_LOW_UTIL_BUCKETS);
        if(page == nullptr) {
            page = GlobalPageGCManager::g_gc_page_manager.allocateFreshPage(this->allocsize, this->realsize);
        }

        return page;
    }

    PageInfo* getFreshPageForEvacuation() noexcept
    {
        PageInfo* page = findLowestUtilPage(high_utilization_buckets, NUM_HIGH_UTIL_BUCKETS);
        if(page == nullptr) {
            page = findLowestUtilPage(low_utilization_buckets, NUM_LOW_UTIL_BUCKETS);
        }
        if(page == nullptr) {
            page = GlobalPageGCManager::g_gc_page_manager.allocateFreshPage(this->allocsize, this->realsize);
        }

        return page;
    }

    void allocatorRefreshEvacuationPage() noexcept
    {
        // If our evac page is full put directly on filled pages list
        if(this->evac_page != nullptr && this->evac_page->freecount == 0) {
            this->evac_page->approx_utilization = 1.0f;
            this->evac_page->next = this->filled_pages;
            this->filled_pages = this->evac_page;
        }

        this->evac_page = this->getFreshPageForEvacuation();
        this->evacfreelist = this->evac_page->freelist;
    }

public:
    GCAllocator(uint16_t allocsize, uint16_t realsize, void (*collect)()) noexcept : freelist(nullptr), evacfreelist(nullptr), alloc_page(nullptr), evac_page(nullptr), allocsize(allocsize), realsize(realsize), pendinggc_pages(nullptr), low_utilization_buckets{}, high_utilization_buckets{}, filled_pages(nullptr), collectfp(collect) { }

    inline size_t getAllocSize() const noexcept
    {
        return this->allocsize;
    }

    // Simple check to see if a page is in alloc/evac/pendinggc pages
    bool checkNonAllocOrGCPage(PageInfo* p) {
        if(p == alloc_page || p == evac_page) {
            return false;
        }

        PageInfo* cur = pendinggc_pages;
        while(cur != nullptr) {
            if(cur == p) {
                return false;
            }
            cur = cur->next;
        }

        return true;
    }

    // Used in case where a page's utilization changed and it isnt being grabbed for evac/alloc
    void deleteOldPage(PageInfo* p) 
    {
        int bucket_index = 0;
        float old_util = p->approx_utilization;

        if(IS_LOW_UTIL(old_util)) {
            GET_BUCKET_INDEX(old_util, NUM_LOW_UTIL_BUCKETS, bucket_index, 0);
            this->deletePageFromBucket(
                &this->low_utilization_buckets[bucket_index], p);        
        }
        else if(IS_HIGH_UTIL(old_util)) {
            GET_BUCKET_INDEX(old_util, NUM_HIGH_UTIL_BUCKETS, bucket_index, 1);
            this->deletePageFromBucket(
                &this->high_utilization_buckets[bucket_index], p);
        }

        // May want to make this traversal not O(n) worst case (sort?)
        else {
            PageInfo* cur = this->filled_pages;
            PageInfo* prev = nullptr;
            while(cur != nullptr && cur != p) {
                prev = cur;
                cur = cur->next;
            }

            if(prev == nullptr) {
                this->filled_pages = cur->next;
            }
            else {
                prev->next = cur->next;
            }
            p->next = nullptr;
            p->left = nullptr;
            p->right = nullptr;
        }
    }

    inline void* allocate(TypeInfoBase* type)
    {
        assert(type->type_size == this->allocsize);

        if(this->freelist == nullptr) [[unlikely]] {
            this->allocatorRefreshPage();
        }

        void* entry = this->freelist;
        this->freelist = this->freelist->next;
        this->alloc_page->freelist = this->alloc_page->freelist->next;
            
        this->alloc_page->freecount--;

        SET_ALLOC_LAYOUT_HANDLE_CANARY(entry, type);
        SETUP_ALLOC_INITIALIZE_FRESH_META(SETUP_ALLOC_LAYOUT_GET_META_PTR(entry), type);

        return SETUP_ALLOC_LAYOUT_GET_OBJ_PTR(entry);
    }

    inline void* allocateEvacuation(TypeInfoBase* type)
    {
        assert(type->type_size == this->allocsize);

        if(this->evacfreelist == nullptr) [[unlikely]] {
            this->allocatorRefreshEvacuationPage();
        }

        void* entry = this->evacfreelist;
        this->evacfreelist = this->evacfreelist->next;
        this->evac_page->freelist = this->evac_page->freelist->next;

        this->evac_page->freecount--;

        SET_ALLOC_LAYOUT_HANDLE_CANARY(entry, type);
        SETUP_ALLOC_INITIALIZE_CONVERT_OLD_META(SETUP_ALLOC_LAYOUT_GET_META_PTR(entry), type);

        return SETUP_ALLOC_LAYOUT_GET_OBJ_PTR(entry);
    }

#ifdef MEM_STATS
    void updateMemStats();
#else
    inline void updateMemStats() {}
#endif

    //Take a page (that may be in of the page sets -- or may not -- if it is a alloc or evac page) and move it to the appropriate page set
    void processPage(PageInfo* p) noexcept;

    //process all the pending gc pages, the current alloc page, and evac page -- reset for next round
    void processCollectorPages() noexcept;

    //May call collection, needs definition in cpp file to prevent cyclic dependicies in fetching gtl_info
    void allocatorRefreshPage() noexcept;
};