#include "allocator.h"
#include "threadinfo.h"

GlobalDataStorage GlobalDataStorage::g_global_data;

PageInfo* PageInfo::initialize(void* block, uint16_t allocsize, uint16_t realsize) noexcept
{
    PageInfo* pp = (PageInfo*)block;

    pp->freelist = nullptr;
    pp->next = nullptr;

    pp->data = ((uint8_t*)block + sizeof(PageInfo));
    pp->allocsize = allocsize;
    pp->realsize = realsize;
    pp->pending_decs_count = 0;
    pp->approx_utilization = 100.0f; // Approx util has not been calculated
    pp->left = nullptr;
    pp->right = nullptr;
    pp->entrycount = (BSQ_BLOCK_ALLOCATION_SIZE - (pp->data - (uint8_t*)pp)) / realsize;
    pp->freecount = pp->entrycount;

    for(int64_t i = pp->entrycount - 1; i >= 0; i--) {
        FreeListEntry* entry = pp->getFreelistEntryAtIndex(i);
        entry->next = pp->freelist;
        pp->freelist = entry;
    }

    return pp;
}

void PageInfo::rebuild() noexcept
{
    this->freelist = nullptr;
    this->freecount = 0;
    
    for(int64_t i = this->entrycount - 1; i >= 0; i--) {
        MetaData* meta = this->getMetaEntryAtIndex(i);
        
        if(GC_SHOULD_FREE_LIST_ADD(meta)) {
            // Just to be safe reset metadata
            RESET_METADATA_FOR_OBJECT(meta, MAX_FWD_INDEX);
            FreeListEntry* entry = this->getFreelistEntryAtIndex(i);
            entry->next = this->freelist;
            this->freelist = entry;
            this->freecount++;
        }
    }

    this->next = nullptr;
}

GlobalPageGCManager GlobalPageGCManager::g_gc_page_manager;

PageInfo* GlobalPageGCManager::allocateFreshPage(uint16_t entrysize, uint16_t realsize) noexcept
{
    GC_MEM_LOCK_ACQUIRE();

    PageInfo* pp = nullptr;
    if(this->empty_pages != nullptr) {
        void* page = this->empty_pages;
        this->empty_pages = this->empty_pages->next;

        pp = PageInfo::initialize(page, entrysize, realsize);
        gtl_info.total_empty_gc_pages--;
    }
    else {
#ifndef ALLOC_DEBUG_MEM_DETERMINISTIC
        void* page = mmap(NULL, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
#else
        ALLOC_LOCK_ACQUIRE();

        void* page = (XAllocPage*)mmap(GlobalThreadAllocInfo::s_current_page_address, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 0, 0);
        GlobalThreadAllocInfo::s_current_page_address = (void*)((uint8_t*)GlobalThreadAllocInfo::s_current_page_address + BSQ_BLOCK_ALLOCATION_SIZE);

        ALLOC_LOCK_RELEASE();    
#endif

        assert(page != MAP_FAILED);
        this->pagetable.pagetable_insert(page);

        pp = PageInfo::initialize(page, entrysize, realsize);
        gtl_info.total_gc_pages++;
    }

    GC_MEM_LOCK_RELEASE();
    return pp;
}

void GCAllocator::processPage(PageInfo* p) noexcept
{
    float old_util = p->approx_utilization;
    float n_util = CALC_APPROX_UTILIZATION(p);
    p->approx_utilization = n_util;
    int bucket_index = 0;

    if(p->entrycount == p->freecount) {
        GlobalPageGCManager::g_gc_page_manager.addNewPage(p);
        gtl_info.total_empty_gc_pages++;
    }
    else if(IS_LOW_UTIL(n_util)) {
        GET_BUCKET_INDEX(n_util, NUM_LOW_UTIL_BUCKETS, bucket_index, 0);
        this->insertPageInBucket(&this->low_utilization_buckets[bucket_index], p, n_util);    
    }
    else if(IS_HIGH_UTIL(n_util)) {
        GET_BUCKET_INDEX(n_util, NUM_HIGH_UTIL_BUCKETS, bucket_index, 1);
        this->insertPageInBucket(&this->high_utilization_buckets[bucket_index], p, n_util);
    }
    // If our page freshly became full we need to gc
    else if(IS_FULL(n_util) && !IS_FULL(old_util)) {
        // We dont want to collect evac page
        if(!(p == this->evac_page)) {
            p->next = this->pendinggc_pages;
            pendinggc_pages = p;
        }
        else {
            p->next = this->filled_pages;
            filled_pages = p;
        }
    }
    // If our page was full before and still full put on filled pages
    else if(IS_FULL(n_util) && IS_FULL(old_util)) {
        p->next = this->filled_pages;
        filled_pages = p;
    }
}

void GCAllocator::processCollectorPages() noexcept
{
    if(this->alloc_page != nullptr) {
        this->alloc_page->rebuild();
        this->processPage(this->alloc_page);

        this->alloc_page = nullptr;
        this->freelist = nullptr;
    }
    
    if(this->evac_page != nullptr) {
        this->processPage(this->evac_page);

        this->evac_page = nullptr;
        this->evacfreelist = nullptr;
    }

    PageInfo* cur = this->pendinggc_pages;
    while(cur != nullptr) {
        PageInfo* next = cur->next;

        cur->rebuild();
        this->processPage(cur);

        cur = next;
    }
    this->pendinggc_pages = nullptr;
}


void GCAllocator::allocatorRefreshPage() noexcept
{
    if(this->alloc_page == nullptr) {
        this->alloc_page = this->getFreshPageForAllocator();
    }
    else {
        // Rotate collection pages
        processPage(this->alloc_page);
        this->alloc_page = nullptr;

        //use BSQ_COLLECTION_THRESHOLD; NOTE: ONLY INCREMENT when we have a full page
        gtl_info.newly_filled_pages_count++;

        // If we exceed our filled pages thresh collect
        if(gtl_info.newly_filled_pages_count == BSQ_COLLECTION_THRESHOLD) {
            if(!gtl_info.disable_automatic_collections) {
                collect();
            }
        }
    
        this->alloc_page = this->getFreshPageForAllocator();
    }

    this->freelist = this->alloc_page->freelist;
}

#ifdef MEM_STATS

inline void process(PageInfo* page)
{
    if (!page) return;
    gtl_info.total_live_bytes += (page->allocsize * (page->entrycount - page->freecount));
}

void traverseBST(PageInfo* node) 
{
    if (!node) return;

    PageInfo* current = node;
    while (current != nullptr) {
        process(current);
        current = current->next;
    }
    
    traverseBST(node->left);
    traverseBST(node->right); 
}

void GCAllocator::updateMemStats() 
{
    //compute stats for filled pages
    PageInfo* filled_it = this->filled_pages;
    while(filled_it != nullptr) {
        process(filled_it);
        filled_it = filled_it->next;
    }

    // Compute stats for high util pages
    for(int i = 0; i < NUM_HIGH_UTIL_BUCKETS; i++) {
        traverseBST(this->high_utilization_buckets[i]);
    }

    // Compute stats for low util pages
    for(int i = 0; i < NUM_LOW_UTIL_BUCKETS; i++) {
        traverseBST(this->low_utilization_buckets[i]);
    }
}

#endif

//TODO: Rework these very funky canary check functions !!!

/*
//Following 3 methods verify integrity of canaries
bool verifyCanariesInBlock(char* block, uint16_t entry_size)
{
    uint64_t* pre_canary = (uint64_t*)(block);
    uint64_t* post_canary = (uint64_t*)(block + ALLOC_DEBUG_CANARY_SIZE + sizeof(MetaData) + entry_size);

    debug_print("[CANARY_CHECK] Verifying canaries for block at %p\n", block);
    debug_print("\tPre-canary value: %lx\n", *pre_canary);
    debug_print("\tPost-canary value: %lx\n", *post_canary);

    if (*pre_canary != ALLOC_DEBUG_CANARY_VALUE || *post_canary != ALLOC_DEBUG_CANARY_VALUE)
    {
        debug_print("[ERROR] Canary corruption detected at block %p\n", block);
        return false;
    }
    return true;
}

void verifyCanariesInPage(PageInfo* page)
{
    FreeListEntry* list = page->freelist;
    uint16_t alloced_blocks = 0;
    uint16_t free_blocks = 0;

    debug_print("[CANARY_CHECK] Verifying canaries for page at %p\n", page);

    for (uint16_t i = 0; i < page->entrycount; i++) {
        char* block_address = PAGE_MASK_EXTRACT_DATA(list) + (i * REAL_ENTRY_SIZE(page->entrysize));
        debug_print("\tChecking block %d at address %p\n", i, block_address);
        MetaData* metadata = (MetaData*)(block_address + ALLOC_DEBUG_CANARY_SIZE);
        debug_print("\tBlock %d metadata state: isalloc=%d\n", i, metadata->isalloc);

        if (metadata->isalloc) {
            debug_print("\tAllocated block detected, verifying canaries...\n");
            alloced_blocks++;
            assert(verifyCanariesInBlock(block_address, page->entrysize));
        }
    }
    debug_print("\n");

    debug_print("[CANARY_CHECK] Verifying freelist for page at %p\n", page);
    while(list){
        debug_print("\tChecking freelist block at %p\n", (void*)list);
        MetaData* metadata = (MetaData*)((char*)list + ALLOC_DEBUG_CANARY_SIZE);
        debug_print("\tFreelist block metadata state: isalloc=%d\n", metadata->isalloc);

        if(metadata->isalloc){
            debug_print("[ERROR] Block in free list was allocated at %p\n", list);
            assert(0);
        }
        free_blocks++;
        list = list->next;
    }   

    // Make sure no blocks are lost
    assert((free_blocks + alloced_blocks) == page->entrycount);

    debug_print("\n");
}

void verifyAllCanaries()
{
    for(int i = 0; i < NUM_BINS; i++) {
        AllocatorBin* bin = getBinForSize(8 * (1 << i));
        PageInfo* alloc_page = bin->alloc_page;
        PageInfo* evac_page = bin->evac_page;

        debug_print("[CANARY_CHECK] Verifying all pages in bin\n");

        while (alloc_page) {
            debug_print("[CANARY_CHECK] Verifying canaries in alloc page at %p\n", alloc_page);
            verifyCanariesInPage(alloc_page);
            alloc_page = alloc_page->next;
        }

        while (evac_page) {
            debug_print("[CANARY_CHECK] Verifying canaries in evac page at %p\n", evac_page);
            verifyCanariesInPage(evac_page);
            evac_page = evac_page->next;
        }
    }
}
*/

//TODO: Rework these very funky canary check functions !!!

/*
//Following 3 methods verify integrity of canaries
bool verifyCanariesInBlock(char* block, uint16_t entry_size)
{
    uint64_t* pre_canary = (uint64_t*)(block);
    uint64_t* post_canary = (uint64_t*)(block + ALLOC_DEBUG_CANARY_SIZE + sizeof(MetaData) + entry_size);

    debug_print("[CANARY_CHECK] Verifying canaries for block at %p\n", block);
    debug_print("\tPre-canary value: %lx\n", *pre_canary);
    debug_print("\tPost-canary value: %lx\n", *post_canary);

    if (*pre_canary != ALLOC_DEBUG_CANARY_VALUE || *post_canary != ALLOC_DEBUG_CANARY_VALUE)
    {
        debug_print("[ERROR] Canary corruption detected at block %p\n", block);
        return false;
    }
    return true;
}

void verifyCanariesInPage(PageInfo* page)
{
    FreeListEntry* list = page->freelist;
    uint16_t alloced_blocks = 0;
    uint16_t free_blocks = 0;

    debug_print("[CANARY_CHECK] Verifying canaries for page at %p\n", page);

    for (uint16_t i = 0; i < page->entrycount; i++) {
        char* block_address = PAGE_MASK_EXTRACT_DATA(list) + (i * REAL_ENTRY_SIZE(page->entrysize));
        debug_print("\tChecking block %d at address %p\n", i, block_address);
        MetaData* metadata = (MetaData*)(block_address + ALLOC_DEBUG_CANARY_SIZE);
        debug_print("\tBlock %d metadata state: isalloc=%d\n", i, metadata->isalloc);

        if (metadata->isalloc) {
            debug_print("\tAllocated block detected, verifying canaries...\n");
            alloced_blocks++;
            assert(verifyCanariesInBlock(block_address, page->entrysize));
        }
    }
    debug_print("\n");

    debug_print("[CANARY_CHECK] Verifying freelist for page at %p\n", page);
    while(list){
        debug_print("\tChecking freelist block at %p\n", (void*)list);
        MetaData* metadata = (MetaData*)((char*)list + ALLOC_DEBUG_CANARY_SIZE);
        debug_print("\tFreelist block metadata state: isalloc=%d\n", metadata->isalloc);

        if(metadata->isalloc){
            debug_print("[ERROR] Block in free list was allocated at %p\n", list);
            assert(0);
        }
        free_blocks++;
        list = list->next;
    }   

    // Make sure no blocks are lost
    assert((free_blocks + alloced_blocks) == page->entrycount);

    debug_print("\n");
}

void verifyAllCanaries()
{
    for(int i = 0; i < NUM_BINS; i++) {
        AllocatorBin* bin = getBinForSize(8 * (1 << i));
        PageInfo* alloc_page = bin->alloc_page;
        PageInfo* evac_page = bin->evac_page;

        debug_print("[CANARY_CHECK] Verifying all pages in bin\n");

        while (alloc_page) {
            debug_print("[CANARY_CHECK] Verifying canaries in alloc page at %p\n", alloc_page);
            verifyCanariesInPage(alloc_page);
            alloc_page = alloc_page->next;
        }

        while (evac_page) {
            debug_print("[CANARY_CHECK] Verifying canaries in evac page at %p\n", evac_page);
            verifyCanariesInPage(evac_page);
            evac_page = evac_page->next;
        }
    }
}
*/
