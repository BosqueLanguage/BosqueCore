#include "alloc.h"

namespace ᐸRuntimeᐳ
{
#if BSQ_ALLOCATOR_USE_MALLOC
    std::map<void*, GCAllocatorImpl*> GCAllocatorImpl::x_all_alloc_to_allocator_map{};
#endif

    thread_local AllocatorThreadLocalInfo tl_alloc_info;
    AllocatorGlobalInfo g_alloc_info;

    PageInfo* PageInfo::setPageMetaData(void* vpp, GCAllocatorImpl* gcalloc, std::thread::id threadid, size_t agectr)
    {
        PageInfo* pp = (PageInfo*)vpp;

        uint32_t p2size = std::bit_ceil(gcalloc->alloctype->slotcount);
        uint32_t p2sizeshift = std::bit_width(p2size) - 1;

        uint32_t objcount = (GC_PAGE_SIZE - sizeof(PageInfo)) / ((p2size + 1) * 8);
        std::memset((void*)((uint8_t*)pp + sizeof(PageInfo)), 0, 8 * objcount);

        pp->typeinfo = gcalloc->alloctype;
        pp->gcalloc = gcalloc;
        pp->threadid = threadid;

        pp->freelistidx = META_FREE_LIST_OOM_SENTINAL;
        pp->freecount = -1;
        pp->esize = objcount;

        pp->mdata = (AtomicGCMetadata*)((uint8_t*)pp + sizeof(PageInfo));
        pp->data = (void**)((void**)pp->mdata + objcount);
        pp->size2shift = p2sizeshift;

        pp->age = agectr;

        return pp;
    }

    void* PageInfo::reset(PageInfo* pp)
    {
        std::memset((void*)((uint8_t*)pp + sizeof(PageInfo)), 0, 8 * pp->esize);

        pp->typeinfo = nullptr;
        pp->gcalloc = nullptr;
        pp->threadid = std::thread::id{};

        pp->freelistidx = META_FREE_LIST_OOM_SENTINAL;
        pp->freecount = -1;
        pp->esize = 0;

        pp->data = nullptr;
        pp->mdata = nullptr;
        pp->size2shift = 0;

        pp->age = 0;

        return (void*)pp;
    }

    void PageInfo::rebuild(size_t agectr)
    {
        this->freelistidx = META_FREE_LIST_OOM_SENTINAL;
        this->freecount = 0;
        this->age = agectr;
 
        for(int64_t i = this->esize - 1; i >= 0; i--) {
            AtomicGCMetadata* meta = this->getMetadataFromIndexInPage(i);

            //
            //TODO: Here is where we want to forward singleton ref counts too!!
            //

            if(!gcIsAllocated(meta) | gcIsYoung(meta)) {
                gcProcessSweep(meta);
                   
                gcSetFreeListBits(meta, this->freelistidx);
                this->freelistidx = i;
                this->freecount++;
            }
        }
    }

#if BSQ_ALLOCATOR_USE_MALLOC
    void runCollect()
    {
        tl_alloc_info.collectfp();
    }
#else
    PageInfo* AllocatorGlobalInfo::getEmptyPage(GCAllocatorImpl* gcalloc)
    {
        std::lock_guard lk(this->g_pages_mutex);

	    if(this->emptypages.empty()) {
            for(size_t i = 0; i < GC_NUM_PAGES_ON_REQ; i++) {
                void* addr = mmap(NULL, GC_PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);

                assert(addr != MAP_FAILED);
                assert(((uintptr_t)addr & GC_PAGE_MASK) == 0);

                this->allocatedpages.insert(addr);
                this->emptypages.push_back(addr);
            }
        }

        void* page = this->emptypages.back();
        this->emptypages.pop_back();        

        return PageInfo::setPageMetaData(page, gcalloc, std::this_thread::get_id(), 0);
    }

    constexpr bool isPageSuitableForAlloc(PageInfo* pp, double availthreshold) 
    {
        return ((double)pp->freecount / (double)pp->esize >= availthreshold) || (pp->freecount > GC_PAGE_AVAILABILITY_COUNT_THRESHOLD);
    }

    PageInfo* GCAllocatorImpl::allocatorPageFinder(double availthreshold, size_t age)
    {
        //try for the nursery recent pages first if NOT evac
        size_t navailchks = 0;
        auto niter = this->pageset.rbegin();
        while(niter != this->pageset.rend() && (*niter)->age == GC_NURSERY_AGE && navailchks < GC_PAGE_CHECK_LIMIT) {
            PageInfo* pp = *niter;
            niter = std::reverse_iterator(this->pageset.erase(std::next(niter).base()));

            pp->rebuild(age);
            
            if(isPageSuitableForAlloc(pp, availthreshold)) {
                return pp;
            }
            
            pp->age = this->generateNextAge();
            this->pageset.insert(pp);
            
            navailchks++;
        }

        //now process age ordered
        size_t availchks = 0;
        auto iter = this->pageset.begin();
        while(iter != this->pageset.end() && availchks < GC_PAGE_CHECK_LIMIT) {
            PageInfo* pp = *iter;
            iter = this->pageset.erase(iter);

            pp->rebuild(age);
            //TODO: check for recycle fully empty pages back to global pool here as well

            if(isPageSuitableForAlloc(pp, availthreshold)) {
                return pp;
            }

            pp->age = this->generateNextAge();
            this->pageset.insert(pp);
    
            availchks++;
        }

        return nullptr;
    }

    void GCAllocatorImpl::allocatorSlowPathRefresh()
    {
        if(this->pendingdelete != nullptr) {
            tl_alloc_info.decsprocessfp(this);
        }

        if(this->allocpage != nullptr) {
            this->filled_pages.push_back(this->allocpage);
            this->allocpage = nullptr;
        }

        if(this->allocatedbytes >= GC_NURSERY_BYTES_COLLECT_THRESHOLD)
        {
            tl_alloc_info.collectfp();
            this->allocatedbytes = 0;
        }

        this->allocpage = this->allocatorPageFinder(GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_ALLOC, GC_NURSERY_AGE);

        if(this->allocpage == nullptr) {
            this->allocpage = g_alloc_info.getEmptyPage(this);
            this->allocpage->rebuild(GC_NURSERY_AGE);
        }

        this->freelistidx = this->allocpage->freelistidx;
        this->allocatedbytes += (this->allocpage->freecount * this->alloctype->bytesize);
    }

    void GCAllocatorImpl::evacuatorSlowPathRefresh()
    {
        if(this->evacpage != nullptr) {
            this->pageset.insert(this->evacpage);
            this->evacpage = nullptr;
        }
        size_t age = this->generateNextAge();

        this->evacpage = this->allocatorPageFinder(GC_PAGE_AVAILABILITY_RATIO_THRESHOLD_EVAC, age);

        if(this->evacpage == nullptr) {
            this->evacpage = g_alloc_info.getEmptyPage(this);
            this->evacpage->rebuild(age);
        }

        this->evaclistidx = this->evacpage->freelistidx;
    }
#endif //BSQ_ALLOCATOR_USE_MALLOC

    void AllocatorThreadLocalInfo::initialize(void** caller_rbp, void (*_collectfp)(), void (*_decsprocessfp)(GCAllocatorImpl*), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs)
    {
        this->native_stack_base = caller_rbp;
        this->collectfp = _collectfp;
        this->decsprocessfp = _decsprocessfp;
        this->gcallocs = gcallocs;
    }
	
    void AllocatorThreadLocalInfo::cleanup()
    {
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
#if BSQ_ALLOCATOR_USE_MALLOC
        if(GCAllocatorImpl::x_all_alloc_to_allocator_map.empty()) {
            return false;
        }

        auto aii = GCAllocatorImpl::x_all_alloc_to_allocator_map.lower_bound(addr);
        if(aii != GCAllocatorImpl::x_all_alloc_to_allocator_map.begin() && aii->first != addr) {
            aii--;
        }

        if(!aii->second->isAddrInValidObject(addr, meta, raddr)) {
            return false;
        }

        return aii->second->isAddrSuitableCategory(meta, raddr);
#else
        auto baseaddr = (void*)((uintptr_t)(addr) & GC_PAGE_ADDR_MASK);
        if(!this->allocatedpages.contains(baseaddr)) {
            return false;
        }

        const PageInfo* pp = (PageInfo*)baseaddr;
        if(pp->typeinfo == nullptr || addr < pp->data) {
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
#endif
    }
}
