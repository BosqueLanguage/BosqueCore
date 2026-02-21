#include "allocator.h"
#include "threadinfo.h"
#include "gc.h"

GlobalDataStorage GlobalDataStorage::g_global_data{};

#ifdef ALLOC_DEBUG_CANARY
#define RESET_META_FROM_FREELIST(E) \
	ZERO_METADATA(PageInfo::getObjectMetadataAligned(reinterpret_cast<uint8_t*>(E) + ALLOC_DEBUG_CANARY_SIZE));
#else
#define RESET_META_FROM_FREELIST(E) \
	ZERO_METADATA(PageInfo::getObjectMetadataAligned(E));
#endif

GCAllocator::GCAllocator(__CoreGC::TypeInfoBase* _alloctype) noexcept :
	alloctype(_alloctype), freelist(nullptr), evacfreelist(nullptr), 
	alloc_page(nullptr), evac_page(nullptr), filled_pages(),
	freshly_filled_pages(), pendinggc_pages()
	, decd_pages(gtl_info.decd_pages)  {}

static void setPageMetaData(PageInfo* pp, GCAllocator* gcalloc) noexcept
{
	std::lock_guard lk(g_alloclock);

	pp->zeroInit();

    pp->typeinfo = gcalloc->getAllocType();
	pp->gcalloc = gcalloc;
	pp->realsize = REAL_ENTRY_SIZE(pp->typeinfo->type_size);
	uint8_t* bpp = reinterpret_cast<uint8_t*>(pp);
    uint8_t* mdataptr = bpp + sizeof(PageInfo);
    pp->mdata = reinterpret_cast<MetaData*>(mdataptr);
    uint8_t* objptr = bpp + BSQ_BLOCK_ALLOCATION_SIZE - pp->realsize;

    int32_t n = 0;
    while(objptr > mdataptr) {
        objptr -= pp->realsize;
        mdataptr += sizeof(MetaData);
        n++;
    }
    GC_INVARIANT_CHECK(n > 0);

    pp->entrycount = n;
    pp->freecount = pp->entrycount;
    pp->data = mdataptr; // First slot after meta
}

PageInfo* PageInfo::initialize(void* block, GCAllocator* gcalloc) noexcept
{ 
	PageInfo* pp = static_cast<PageInfo*>(block);	
	setPageMetaData(pp, gcalloc);
    
	for(int64_t i = pp->entrycount - 1; i > 0; i--) {
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
 
    for(int64_t i = this->entrycount - 1; i > 0; i--) {
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
	
	size_t freed = this->freecount >= pfree ? 
		(this->freecount - pfree) * this->typeinfo->type_size : 0;
	return freed;
}

void PageInfo::removeSelfFromStorage()
{
	GC_INVARIANT_CHECK(this->owner != nullptr);
	this->owner.load()->remove(this);
	this->owner = nullptr;
}

GlobalPageGCManager GlobalPageGCManager::g_gc_page_manager;

PageInfo* GlobalPageGCManager::getFreshPageFromOS(GCAllocator* gcalloc)
{
	std::unique_lock lk(g_alloclock);
#ifndef ALLOC_DEBUG_MEM_DETERMINISTIC
	void* page = mmap(NULL, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    assert(((uintptr_t)page & PAGE_MASK) == 0 && "Address is not aligned to page boundary!");
#else
    void* page = mmap(GlobalThreadAllocInfo::s_current_page_address, BSQ_BLOCK_ALLOCATION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 0, 0);
    GlobalThreadAllocInfo::s_current_page_address = (void*)((uint8_t*)GlobalThreadAllocInfo::s_current_page_address + BSQ_BLOCK_ALLOCATION_SIZE);
#endif

    assert(page != MAP_FAILED);

	lk.unlock();

	this->pagetableInsert(page);

    PageInfo* pp = PageInfo::initialize(page, gcalloc);

    UPDATE_TOTAL_PAGES(gtl_info.memstats, +=, 1);
	
	return pp;
}

PageInfo* GlobalPageGCManager::tryGetEmptyPage(GCAllocator* gcalloc)
{
	std::lock_guard lk(g_gcmemlock);

	PageInfo* pp = nullptr;
    if(!this->empty_pages.empty()) {
        void* page = this->empty_pages.pop();
        pp = PageInfo::initialize(page, gcalloc);
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
		this->pendinggc_pages.push(this->alloc_page);
        this->alloc_page = nullptr;
        this->freelist = nullptr;
    }
    
    if(this->evac_page != nullptr) {
		this->pendinggc_pages.push(this->evac_page);
        this->evac_page = nullptr;
        this->evacfreelist = nullptr;
    }

	// Place pages who are freshly filled (allocated between last collection
	// and current) onto the pendinggc list for lazy rebuilding
	while(!this->freshly_filled_pages.empty()) {
		PageInfo* p = this->freshly_filled_pages.pop();
		this->pendinggc_pages.push(p);
	} 
}


PageInfo* GCAllocator::tryGetPendingGCPage(const float max_util) noexcept
{
	PageInfo* pp = nullptr;
	while(!this->pendinggc_pages.empty()) {
		PageInfo* p = this->pendinggc_pages.pop();
		p->rebuild();

		if(p->approx_utilization < max_util) {
			pp = p;
			break;
		}
		else {
			this->processPage(p);	
		}
	}

	return pp;
}

// NOTE we need to monitor perf here, we now have significantly more
// allocators so the likelyhood of burning through a lot of pages before
// finding one that is either empty or of the correct type is higher
PageInfo* GCAllocator::tryGetPendingRebuildPage(const float max_util)
{	
	PageInfo* pp = nullptr;
	while(!gtl_info.decd_pages.empty()) {
		PageInfo* p = gtl_info.decd_pages.pop();
		p->rebuild();

		// Move pages that are not correct type or too full
		if((p->typeinfo != this->alloctype && p->freecount != p->entrycount)
			|| p->approx_utilization > max_util)
		{
			p->gcalloc->processPage(p);
		}
	    else {
			if(p->freecount == p->entrycount) {
				p = PageInfo::initialize(p, this);
			}
			pp = p;

			break;		
		}	
	}

	return pp;
}

// We always want to get pending gc/pages with freshly dead objects from rc
// decs before others as they have not been rebuit yet; rebuilding then 
// allocating right away will help keep their freelist cached
PageInfo* GCAllocator::getFreshPageForAllocator() noexcept
{
	PageInfo* page = this->tryGetPendingGCPage(LOW_UTIL_THRESH);
   	if(page == nullptr) {
		page = this->tryGetPendingRebuildPage(LOW_UTIL_THRESH);
    }
	if(page == nullptr) { 
		page = this->getLowestLowUtilPage();
	}
    if(page == nullptr) {
        page = GlobalPageGCManager::g_gc_page_manager.tryGetEmptyPage(this);
    }
	if(page == nullptr) {
		page = GlobalPageGCManager::g_gc_page_manager.getFreshPageFromOS(this);	
	}

    return page;
}

PageInfo* GCAllocator::getFreshPageForEvacuation() noexcept
{

	PageInfo* page = this->tryGetPendingRebuildPage(HIGH_UTIL_THRESH);
   	if(page == nullptr) { 
		page = this->getLowestHighUtilPage();
	}	
    if(page == nullptr) {
        page = this->getLowestLowUtilPage();
    } 
    if(page == nullptr) {
        page = GlobalPageGCManager::g_gc_page_manager.tryGetEmptyPage(this);
    }	
	if(page == nullptr) {
		page = GlobalPageGCManager::g_gc_page_manager.getFreshPageFromOS(this);
	}

	return page;
}

void GCAllocator::allocatorRefreshAllocationPage()noexcept
{
    if(this->alloc_page != nullptr) {
        gtl_info.updateNurseryUsage(this->alloc_page);
        if(gtl_info.nursery_usage >= BSQ_FULL_NURSERY_THRESHOLD 
			&& !gtl_info.disable_automatic_collections) 
		{ 
            gtl_info.nursery_usage = 0.0f;
            gtl_info.collectfp();
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
    UPDATE_TOTAL_LIVE_BYTES(gtl_info.memstats, +=, 
		(page->typeinfo->type_size * (page->entrycount - freecount)));
    UPDATE_TOTAL_LIVE_OBJECTS(gtl_info.memstats, +=, 
		(page->entrycount - freecount));
}

void GCAllocator::updateMemStats() noexcept
{
    UPDATE_TOTAL_ALLOC_COUNT(gtl_info.memstats, +=, GET_ALLOC_COUNT(this));
    UPDATE_TOTAL_ALLOC_MEMORY(gtl_info.memstats, +=, GET_ALLOC_MEMORY(this));
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

    if(TOTAL_LIVE_BYTES(gtl_info.memstats) > MAX_LIVE_HEAP(gtl_info.memstats)) {
        UPDATE_MAX_LIVE_HEAP(gtl_info.memstats, =, 
			TOTAL_LIVE_BYTES(gtl_info.memstats));
    }
}

#endif

//
// TODO: Might be a good idea to add some canary verify
// functions
//
