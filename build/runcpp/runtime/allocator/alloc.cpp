#include "alloc.h"

namespace ᐸRuntimeᐳ
{
    thread_local AllocatorThreadLocalInfo tl_alloc_info;
    AllocatorGlobalInfo g_alloc_info;

    PageInfo* PageInfo::setPageMetaData(void* vpp, GCAllocatorImpl* gcalloc, std::thread::id threadid)
    {
        PageInfo* pp = (PageInfo*)vpp;

        uint32_t p2size = std::bit_ceil(gcalloc->alloctype->slotcount);
        uint32_t p2sizeshift = std::bit_width(p2size) - 1;

        uint32_t objcount = (GC_PAGE_SIZE - sizeof(PageInfo)) / ((p2size + 1) * 8);
        std::memset((void*)((uint8_t*)pp + sizeof(PageInfo)), 0, 8 * objcount);

        pp->typeinfo = gcalloc->alloctype;
        pp->gcalloc = gcalloc;
        pp->threadid = threadid;

        pp->freelist = nullptr;

        pp->freecount = -1;
        pp->esize = objcount;

        pp->mdata = (AtomicGCMetadata*)((uint8_t*)pp + sizeof(PageInfo));
        pp->data = (void**)((void**)pp->mdata + objcount);
        pp->p2size = p2size;
        pp->size2shift = p2sizeshift;

        return pp;
    }

    void* PageInfo::reset()
    {
        std::memset((void*)((uint8_t*)this + sizeof(PageInfo)), 0, 8 * this->esize);

        this->typeinfo = nullptr;
        this->gcalloc = nullptr;
        this->threadid = std::thread::id{};

        this->freelist = nullptr;

        this->freecount = -1;
        this->esize = 0;

        this->data = nullptr;
        this->mdata = nullptr;
        this->size2shift = 0;

        return (void*)this;
    }

    void PageInfo::rebuild()
    {
        this->gcFreeListReset();
 
        for(int64_t i = this->esize - 1; i >= 0; i--) {
            AtomicGCMetadata* meta = this->getMetadataFromIndexInPage(i);

            //
            //TODO: Here is where we want to forward singleton ref counts too!!
            //      Don't reclaim but forward + update parent (might have root ref now) so stash for checking after GC ops
            //

            if(!gcIsAllocated(meta) | gcIsYoung(meta)) {
                gcProcessSweep(meta);
#if GC_MEMORY_CLEAR_FEATURE
                std::memset(this->getObjectFromIndexInPage(i), 0, this->p2size * 8);
#endif

                this->gcFreeListPush(i);
            }
        }
    }

#if GC_DETERMINISTIC_ADDRESS_FEATURE
    //Hardcoded address that we start deterministic page allocations from to make debugging/diagnostics easier
    void* g_current_page_address = (void*)(0x7ffff7f32000); 
#endif
    
    PageInfo* AllocatorGlobalInfo::getEmptyPage(GCAllocatorImpl* gcalloc)
    {
        std::lock_guard lk(this->g_pages_mutex);

	    if(this->emptypages.empty()) {
            for(size_t i = 0; i < GC_NUM_PAGES_ON_REQ; i++) {
#if !GC_DETERMINISTIC_ADDRESS_FEATURE
                void* addr = mmap(NULL, GC_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
#else
                void* addr = mmap(g_current_page_address, GC_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 0, 0);
                g_current_page_address = (void*)((uint8_t*)g_current_page_address + GC_PAGE_SIZE);
#endif
                assert(addr != MAP_FAILED);

                this->allocatedpages.insert(addr);
                this->emptypages.push_back(addr);
            }
        }

        void* page = this->emptypages.back();
        this->emptypages.pop_back();        

        return PageInfo::setPageMetaData(page, gcalloc, std::this_thread::get_id());
    }

    inline bool isPageSuitableForAlloc(PageInfo* pp, double availthreshold) 
    {
        return ((double)pp->freecount / (double)pp->esize >= availthreshold) || (pp->freecount > GC_PAGE_AVAILABILITY_COUNT_THRESHOLD);
    }

    PageInfo* GCAllocatorImpl::allocatorNurseryPageFinder(double availthreshold)
    {
        size_t navailchks = 0;
        auto niter = this->hot_nursery_pages.begin();
        while(niter != this->hot_nursery_pages.end() && navailchks < GC_PAGE_CHECK_NURSERY_LIMIT) {
            PageInfo* pp = *niter;

#if !GC_CLEAR_EAGER_FEATURE
            pp->rebuild();
#endif

            if(isPageSuitableForAlloc(pp, availthreshold)) {
                this->hot_nursery_pages.erase(niter);
                return pp;
            }
            
            niter = this->hot_nursery_pages.erase(niter);
            this->pageset.push_back(pp);

            navailchks++;
        }

        return nullptr;
    }

    PageInfo* GCAllocatorImpl::allocatorGeneralPageFinder(double availthreshold)
    {
        size_t availchks = 0;
        auto iter = this->pageset.begin();
        while(iter != this->pageset.end() && availchks < GC_PAGE_CHECK_GENERAL_LIMIT) {
            PageInfo* pp = *iter;
            pp->rebuild();
            //TODO: check for recycle fully empty pages back to global pool here as well

            if(isPageSuitableForAlloc(pp, availthreshold)) {
                this->pageset.erase(iter);
                return pp;
            }

            iter++;
            availchks++;
        }

        return nullptr;
    }

    void GCAllocatorImpl::allocatorSlowPathRefresh()
    {
        if(this->allocpage != nullptr) {
            this->filled_pages.push_back(this->allocpage);
            this->allocpage = nullptr;
        }

        if(this->allocatedbytes >= GC_NURSERY_BYTES_COLLECT_THRESHOLD)
        {
            tl_alloc_info.collectfp();
            this->allocatedbytes = 0;
        }
        else {
            if(!tl_alloc_info.pendingdelete.empty()) {
                tl_alloc_info.procdecsfp(GC_DELETE_PENDING_PROCESS_BYTES_INCREMENTAL);
            }
        }

        this->allocpage = this->allocatorNurseryPageFinder(GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC);

        if(this->allocpage == nullptr) {
            this->allocpage = this->allocatorGeneralPageFinder(GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC);
        }

        if(this->allocpage == nullptr) {
            GC_METRICS_BASIC_OP(g_memstats.processallocpage());

            this->allocpage = g_alloc_info.getEmptyPage(this);
            this->allocpage->rebuild();
        }

        this->nextalloc = this->allocpage->gcLoadFreeNext();
        this->allocatedbytes += (this->allocpage->freecount * (this->alloctype->bytesize * 8));
    }

    void GCAllocatorImpl::evacuatorSlowPathRefresh()
    {
        if(this->evacpage != nullptr) {
            this->pageset.push_back(this->evacpage);
            this->evacpage = nullptr;
        }
        this->evacpage = this->allocatorGeneralPageFinder(GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_EVAC);

        if(this->evacpage == nullptr) {
            GC_METRICS_BASIC_OP(g_memstats.processallocpage());

            this->evacpage = g_alloc_info.getEmptyPage(this);
            this->evacpage->rebuild();
        }

        this->nextevac = this->evacpage->gcLoadFreeNext();
    }

    void AllocatorThreadLocalInfo::initialize(void** caller_rbp, void(*_procdecsfp)(size_t), void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs)
    {
        this->native_stack_base = caller_rbp;
        this->procdecsfp = _procdecsfp;
        this->collectfp = _collectfp;
        this->gcallocs = gcallocs;
    }
	
    void AllocatorThreadLocalInfo::cleanup()
    {
        g_memstats.dump(std::cout);

        for(auto iter = this->gcallocs.begin(); iter != this->gcallocs.end(); iter++) {
            iter->second->cleanup();
        }
    
        this->gcallocs.clear();
    }

    void AllocatorGlobalInfo::initializeGlobalRegion(void* data)
    {
        this->g_globals = data;
        this->g_globals_lastproc = (void**)this->g_globals;
        this->g_globals_end = (void**)this->g_globals;
    }
    
    void* AllocatorGlobalInfo::getGlobalRegionStorageOfSize(size_t k)
    {
        void* slot = (void*)this->g_globals_end;
        this->g_globals_end = (void**)((uint8_t*)this->g_globals_end + k);

        return slot;
    }

    bool AllocatorGlobalInfo::loadGlobalRootsToProc(std::vector<void*>& possibleroots)
    {
        this->g_globals_mutex.lock();
        if(this->g_globals_lastproc == this->g_globals_end) {
            this->g_globals_mutex.unlock();
            return false;
        }

        std::copy(this->g_globals_lastproc, this->g_globals_end, std::back_inserter(possibleroots));
        return true;
    }

    void AllocatorGlobalInfo::unloadGlobalRootsFromProc(bool processed)
    {
        if(processed) {
            this->g_globals_lastproc = this->g_globals_end;
            this->g_globals_mutex.unlock();
        }
    }

    bool AllocatorGlobalInfo::isAllocatedAddress(void* addr, AtomicGCMetadata*& meta, void*& raddr)
    {
        auto baseaddr = (void*)((uintptr_t)(addr) & GC_PAGE_ADDR_MASK);
        if(!this->allocatedpages.contains(baseaddr)) {
            return false;
        }

        const PageInfo* pp = (PageInfo*)baseaddr;
        if(pp->typeinfo == nullptr || addr < pp->data || (void*)((void**)pp->data + (pp->esize << pp->size2shift)) <= addr) {
            //This page is not in use OR the pointer is not into the data section of the page
            return false;
        }

        auto idx = pp->getIndexForObjectInPage(addr);

        meta = pp->getMetadataFromIndexInPage(idx);
        raddr = pp->getObjectFromIndexInPage(idx);

        if(!gcIsAllocated(meta)) {
            return false;
        }

        std::thread::id objtid = gcGetThreadId(raddr);
        if(gcIsYoung(meta) && objtid != std::this_thread::get_id()) {
            return false;
        }

        return true;
    }
}
