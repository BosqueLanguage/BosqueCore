#include "allocator.h"
#include "threadinfo.h"

GlobalDataStorage GlobalDataStorage::g_global_data{};

#ifdef ALLOC_DEBUG_CANARY
#define RESET_META_FROM_FREELIST(E) ZERO_METADATA(reinterpret_cast<MetaData*>(reinterpret_cast<uint8_t*>(E) + ALLOC_DEBUG_CANARY_SIZE));
#else
#define RESET_META_FROM_FREELIST(E) ZERO_METADATA(reinterpret_cast<MetaData*>(entry));
#endif

PageInfo* PageInfo::initialize(void* block, uint16_t allocsize, uint16_t realsize) noexcept
{
    PageInfo* pp = (PageInfo*)block;

    pp->freelist = nullptr;
    pp->data = ((uint8_t*)block + sizeof(PageInfo));
    pp->allocsize = allocsize;
    pp->realsize = realsize;
    pp->approx_utilization = 0.0f;
	pp->visited = false;

    pp->owner = nullptr;
    pp->prev = nullptr;
    pp->next = nullptr;

    pp->entrycount = (BSQ_BLOCK_ALLOCATION_SIZE - (pp->data - (uint8_t*)pp)) / realsize;
    pp->freecount = pp->entrycount;

    for(int64_t i = pp->entrycount - 1; i >= 0; i--) {
        FreeListEntry* entry = pp->getFreelistEntryAtIndex(i);
        RESET_META_FROM_FREELIST(entry);
        entry->next = pp->freelist;
        pp->freelist = entry;
    }

    return pp;
}

size_t PageInfo::rebuild() noexcept
{
	uint16_t pfree = this->freecount;

    this->freelist = nullptr;
    this->freecount = 0;
 
    for(int64_t i = this->entrycount - 1; i >= 0; i--) {
        MetaData* m = this->getMetaEntryAtIndex(i);

        GC_CHECK_BOOL_BYTES(m);

        if(GC_SHOULD_FREE_LIST_ADD(m)) {
            ZERO_METADATA(m);
            FreeListEntry* entry = this->getFreelistEntryAtIndex(i);
            entry->next = this->freelist;
            this->freelist = entry;
            this->freecount++;
        }
    }
    this->approx_utilization = CALC_APPROX_UTILIZATION(this);
	
	size_t freed = this->freecount >= pfree ? (this->freecount - pfree) * this->allocsize : 0;
	return freed;
}

GlobalPageGCManager GlobalPageGCManager::g_gc_page_manager;

PageInfo* GlobalPageGCManager::getFreshPageFromOS(uint16_t entrysize, uint16_t realsize)
{
#ifndef ALLOC_DEBUG_MEM_DETERMINISTIC
	void* page = mmap(NULL, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    assert(((uintptr_t)page & PAGE_MASK) == 0 && "Address is not aligned to page boundary!");
#else
    ALLOC_LOCK_ACQUIRE();

    void* page = mmap(GlobalThreadAllocInfo::s_current_page_address, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 0, 0);
    GlobalThreadAllocInfo::s_current_page_address = (void*)((uint8_t*)GlobalThreadAllocInfo::s_current_page_address + BSQ_BLOCK_ALLOCATION_SIZE);

    ALLOC_LOCK_RELEASE();    
#endif

    assert(page != MAP_FAILED);
    this->pagetableInsert(page);

    PageInfo* pp = PageInfo::initialize(page, entrysize, realsize);

    UPDATE_TOTAL_PAGES(+=, 1);
	
	return pp;
}

PageInfo* GlobalPageGCManager::tryGetEmptyPage(uint16_t entrysize, uint16_t realsize)
{
	PageInfo* pp = nullptr;
    if(!this->empty_pages.empty()) {
        void* page = this->empty_pages.pop();
        pp = PageInfo::initialize(page, entrysize, realsize);
    }

	return pp;
}

void GCAllocator::processPage(PageInfo* p) noexcept
{
    if(p->entrycount == p->freecount) {
        GlobalPageGCManager::g_gc_page_manager.addNewPage(p); 
        return ;
    }
    
    if(this->insertPageInBucket(p)) {
        return ;
    }
     
    this->filled_pages.push(p);
}

void GCAllocator::processCollectorPages(BSQMemoryTheadLocalInfo* tinfo) noexcept
{
    if(this->alloc_page != nullptr) {
        tinfo->bytes_freed += this->alloc_page->rebuild();
        this->processPage(this->alloc_page);

        this->alloc_page = nullptr;
        this->freelist = nullptr;
    }
    
    if(this->evac_page != nullptr) {
        tinfo->bytes_freed += this->evac_page->rebuild();
        this->processPage(this->evac_page);

        this->evac_page = nullptr;
        this->evacfreelist = nullptr;
    }

    while(!this->pendinggc_pages.empty()) {
        PageInfo* p = this->pendinggc_pages.pop();
        tinfo->bytes_freed += p->rebuild();
        this->processPage(p);
    }
}
	
PageInfo* GCAllocator::tryGetPendingRebuildPage(float max_util)
{	
	PageInfo* pp = nullptr;
	while(!gtl_info.decd_pages.isEmpty()) {
		PageInfo* p = gtl_info.decd_pages.pop_front();	
		p->visited = false;	

		// alloc, evac, or pendinggc pages will be rebuilt in next collection
		GCAllocator* gcalloc = gtl_info.getAllocatorForPageSize(p);
		if(p == gcalloc->alloc_page || p == gcalloc->evac_page || p->owner == &gcalloc->pendinggc_pages) {
			continue;
		}

		p->owner->remove(p);
		p->rebuild();

		// Move pages who are not correct size
		if((p->allocsize != this->allocsize && p->freecount != p->entrycount)
			|| p->approx_utilization > max_util) {
				gcalloc->processPage(p);
		}
	    else {
			if(p->freecount == p->entrycount) {
				p = PageInfo::initialize(p, this->allocsize, this->realsize);
			}
			pp = p;

			break;		
		}	
	}

	return pp;
}

PageInfo* GCAllocator::getFreshPageForAllocator() noexcept
{
    PageInfo* page = this->getLowestLowUtilPage();
    if(page == nullptr) {
        page = GlobalPageGCManager::g_gc_page_manager.tryGetEmptyPage(this->allocsize, this->realsize);
    }
	if(page == nullptr) {
		page = this->tryGetPendingRebuildPage(LOW_UTIL_THRESH);
    }
	if(page == nullptr) {
		page = GlobalPageGCManager::g_gc_page_manager.getFreshPageFromOS(this->allocsize, this->realsize);	
	}

    return page;
}

PageInfo* GCAllocator::getFreshPageForEvacuation() noexcept
{
    PageInfo* page = this->getLowestHighUtilPage();
    if(page == nullptr) {
        page = this->getLowestLowUtilPage();
    } 
    if(page == nullptr) {
        page = GlobalPageGCManager::g_gc_page_manager.tryGetEmptyPage(this->allocsize, this->realsize);
    }
	if(page == nullptr) {
		page = this->tryGetPendingRebuildPage(HIGH_UTIL_THRESH);
    }
	if(page == nullptr) {
		page = GlobalPageGCManager::g_gc_page_manager.getFreshPageFromOS(this->allocsize, this->realsize);
	}

	return page;
}

void GCAllocator::allocatorRefreshAllocationPage(__CoreGC::TypeInfoBase* typeinfo) noexcept
{
    // Just to make sure high 32 bits are stored
    if(g_typeptr_high32 == 0) {
        const_cast<uint64_t&>(g_typeptr_high32) = reinterpret_cast<uint64_t>(typeinfo) >> NUM_TYPEPTR_BITS;
    }

    if(this->alloc_page != nullptr) {
        gtl_info.updateNurseryUsage(this->alloc_page);
        if(gtl_info.nursery_usage >= BSQ_FULL_NURSERY_THRESHOLD && !gtl_info.disable_automatic_collections) { 
            gtl_info.nursery_usage = 0.0f;
            this->collectfp();
        }
        else {
            this->rotateFullAllocPage();
        }
    }

    this->alloc_page = this->getFreshPageForAllocator();
    this->freelist = this->alloc_page->freelist;
}

void GCAllocator::allocatorRefreshEvacuationPage() noexcept
{
    if(this->evac_page != nullptr) {
        this->filled_pages.push(this->evac_page);
    }

    this->evac_page = this->getFreshPageForEvacuation();
    this->evacfreelist = this->evac_page->freelist;
}

#ifdef MEM_STATS

static uint64_t getPageFreeCount(PageInfo* p) noexcept 
{
    uint64_t freecount = 0;
    for(size_t i = 0; i < p->entrycount; i++) {
        void* obj = p->getObjectAtIndex(i); 
		MetaData* m = GC_GET_META_DATA_ADDR(obj);
		if(!GC_IS_ALLOCATED(m)) {
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
    UPDATE_TOTAL_LIVE_BYTES(+=, (page->allocsize * (page->entrycount - freecount)));
    UPDATE_TOTAL_LIVE_OBJECTS(+=, (page->entrycount - freecount));
}

void GCAllocator::updateMemStats() noexcept
{
    UPDATE_TOTAL_ALLOC_COUNT(+=, GET_ALLOC_COUNT(this));
    UPDATE_TOTAL_ALLOC_MEMORY(+=, GET_ALLOC_MEMORY(this));
    RESET_ALLOC_STATS(this);

    //compute stats for filled pages
    for(PageInfo* p : this->filled_pages) {
        process(p);
    }

    // Compute stats for high util pages
    for(int i = 0; i < NUM_HIGH_UTIL_BUCKETS; i++) {
        for(PageInfo* p : this->high_util_buckets[i]) {
            process(p);
        }
    }

    // Compute stats for low util pages
    for(int i = 0; i < NUM_LOW_UTIL_BUCKETS; i++) {
        for(PageInfo* p : this->low_util_buckets[i]) {
            process(p);
        }
    }

    if(TOTAL_LIVE_BYTES() > MAX_LIVE_HEAP()) {
        UPDATE_MAX_LIVE_HEAP(=, TOTAL_LIVE_BYTES());
    }
}

#endif

//
// TODO: Might be a good idea to add some canary verify
// functions
//
