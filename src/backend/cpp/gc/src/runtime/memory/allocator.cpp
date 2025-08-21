#include "allocator.h"
#include "threadinfo.h"
#include "../support/pagebst.h"

GlobalDataStorage GlobalDataStorage::g_global_data{};

PageInfo* PageInfo::initialize(void* block, uint16_t allocsize, uint16_t realsize) noexcept
{
    PageInfo* pp = (PageInfo*)block;

    pp->freelist = nullptr;
    pp->next = nullptr;
    pp->data = ((uint8_t*)block + sizeof(PageInfo));
    pp->allocsize = allocsize;
    pp->realsize = realsize;
    pp->approx_utilization = 0.0f;
    pp->pending_decs_count = 0;
    pp->seen = false;
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
    this->seen = false;
    this->next = nullptr;
    this->left = nullptr;
    this->right = nullptr;
    
    for(int64_t i = this->entrycount - 1; i >= 0; i--) {
        MetaData* meta = this->getMetaEntryAtIndex(i);
        
        assert(meta->ref_count >= 0);

        if(GC_SHOULD_FREE_LIST_ADD(meta)) {
            FreeListEntry* entry = this->getFreelistEntryAtIndex(i);
            entry->next = this->freelist;
            this->freelist = entry;
            this->freecount++;
        }
    }

    this->approx_utilization = CALC_APPROX_UTILIZATION(this);
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
        UPDATE_TOTAL_EMPTY_GC_PAGES(gtl_info, --);
    }
    else {
#ifndef ALLOC_DEBUG_MEM_DETERMINISTIC
        void* page = mmap(NULL, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
#else
        ALLOC_LOCK_ACQUIRE();

        void* page = mmap(GlobalThreadAllocInfo::s_current_page_address, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 0, 0);
        GlobalThreadAllocInfo::s_current_page_address = (void*)((uint8_t*)GlobalThreadAllocInfo::s_current_page_address + BSQ_BLOCK_ALLOCATION_SIZE);

        ALLOC_LOCK_RELEASE();    
#endif

        assert(page != MAP_FAILED);
        this->pagetable.pagetable_insert(page);

        pp = PageInfo::initialize(page, entrysize, realsize);
        UPDATE_TOTAL_GC_PAGES(gtl_info, ++);
    }

    GC_MEM_LOCK_RELEASE();
    return pp;
}

void GCAllocator::processPage(PageInfo* p) noexcept
{
    if(p->entrycount == p->freecount) {
        GlobalPageGCManager::g_gc_page_manager.addNewPage(p);
        UPDATE_TOTAL_EMPTY_GC_PAGES(gtl_info, ++);

        return ;
    }
    
    if(insertPageInBucket(this, p)) {
        return ;
    }
    
    // Full page
    if(p == this->evac_page) {
        p->next = this->filled_pages;
        filled_pages = p;
    }
    else {
        p->next = this->pendinggc_pages;
        pendinggc_pages = p;
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
        this->evac_page->rebuild();
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

PageInfo* GCAllocator::getFreshPageForAllocator() noexcept
{
    PageInfo* page = getLowestUtilPageLow(this);
    if(page == nullptr) {
        page = GlobalPageGCManager::g_gc_page_manager.allocateFreshPage(this->allocsize, this->realsize);
    }

    return page;
}

PageInfo* GCAllocator::getFreshPageForEvacuation() noexcept
{
    PageInfo* page = getLowestUtilPageHigh(this);
    if(page == nullptr) {
        page = getLowestUtilPageLow(this);
    }
    if(page == nullptr) {
        page = GlobalPageGCManager::g_gc_page_manager.allocateFreshPage(this->allocsize, this->realsize);
    }

    return page;
}

void GCAllocator::allocatorRefreshAllocationPage() noexcept
{
    if(this->alloc_page == nullptr) {
        this->alloc_page = this->getFreshPageForAllocator();
    }
    else {
        gtl_info.newly_filled_pages_count++;

        // If we exceed our filled pages thresh collect
        if(gtl_info.newly_filled_pages_count == BSQ_COLLECTION_THRESHOLD) {
            if(!gtl_info.disable_automatic_collections) {
                this->collectfp();
            }
        }
        else {
            // Rotate collection pages
            this->alloc_page->next = this->pendinggc_pages;
            this->pendinggc_pages = this->alloc_page;            
        }
    
    
        this->alloc_page = this->getFreshPageForAllocator();
    }

    this->freelist = this->alloc_page->freelist;
}

void GCAllocator::allocatorRefreshEvacuationPage() noexcept
{
    if(this->evac_page != nullptr) {
        this->evac_page->next = this->filled_pages;
        this->filled_pages = this->evac_page;
    }

    this->evac_page = this->getFreshPageForEvacuation();
    this->evacfreelist = this->evac_page->freelist;
}

#ifdef MEM_STATS

static uint64_t getPageFreeCount(PageInfo* p) noexcept 
{
    uint64_t freecount = 0;
    for(int64_t i = 0; i < p->entrycount; i++) {
        MetaData* meta = p->getMetaEntryAtIndex(i); 
        if(!meta->isalloc) {
            freecount++;
        }
    }

    return freecount;
}

static inline void process(PageInfo* page) noexcept
{
    if(!page) {
        return;
    }
   
    uint64_t freecount = getPageFreeCount(page);
    UPDATE_TOTAL_LIVE_BYTES(gtl_info, +=, (page->allocsize * (page->entrycount - freecount)));
}

static void traverseBST(PageInfo* node) noexcept
{
    if(!node) {
        return;
    }

    PageInfo* current = node;
    while (current != nullptr) {
        process(current);
        current = current->next;
    }
    
    traverseBST(node->left);
    traverseBST(node->right); 
}

void GCAllocator::updateMemStats() noexcept
{
    //compute stats for filled pages
    PageInfo* filled_it = this->filled_pages;
    while(filled_it != nullptr) {
        process(filled_it);
        filled_it = filled_it->next;
    }

    // Compute stats for high util pages
    for(int i = 0; i < NUM_HIGH_UTIL_BUCKETS; i++) {
        traverseBST(this->high_util_buckets[i]);
    }

    // Compute stats for low util pages
    for(int i = 0; i < NUM_LOW_UTIL_BUCKETS; i++) {
        traverseBST(this->low_util_buckets[i]);
    }
}

#endif

//
// TODO: Might be a good idea to add some canary verify
// functions
//