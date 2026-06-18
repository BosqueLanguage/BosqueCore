#pragma once

#include "memory.h"

namespace ᐸRuntimeᐳ
{
    constexpr size_t MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE = 8192; //8KB blocks for buffer allocation

    class GCAllocatorImpl;
    class GCPageList;

    ////////////////////////////////////////////
    // Page Layout:
    // | Page Metadata | Objects Metadata | Data |
    class PageInfo
    {
    public:
        const TypeInfo* typeinfo; //all entries are of same type
        GCAllocatorImpl* gcalloc; //alloc for this->typeinfo
        std::thread::id threadid;

        void* freelist; // Free list for this page
        int64_t freecount;
        int64_t esize; //max number of entries in this page

        void* data; //start of the data block
        AtomicGCMetadata* mdata; // Meta data is stored out-of-band
        uint32_t p2size; //power of 2 rounded (slot size) of the type stored in this page
        uint32_t size2shift; //shift bits for power of 2 rounded (slot size) of the type stored in this page

        constexpr static PageInfo* extractPageFromPointer(void* p) 
        {
            return (PageInfo*)((uintptr_t)(p) & GC_PAGE_ADDR_MASK);
        }

        constexpr uint16_t getIndexForObjectInPage(void* obj) const
        { 
            return (uint16_t)(((void**)obj - (void**)this->data) >> this->size2shift);
        }

        constexpr void* getObjectFromIndexInPage(size_t idx) const
        {
            return (void*)((void**)this->data + (idx << this->size2shift));
        }

        constexpr uint16_t getIndexForMetadataInPage(void* obj) const
        { 
            return (uint16_t)(((void**)obj - (void**)this->data) >> this->size2shift);
        }

        constexpr AtomicGCMetadata* getMetadataFromIndexInPage(size_t idx) const
        {
            return this->mdata + idx;
        }

        constexpr static AtomicGCMetadata* getMetadataForObj(void* obj)
        {
            PageInfo* pp = extractPageFromPointer(obj);
            return pp->mdata + pp->getIndexForMetadataInPage(obj);
        }

        constexpr void gcFreeListReset() 
        {
            this->freelist = nullptr;
            this->freecount = 0;
        }

        constexpr void gcFreeListPush(uint16_t index) 
        {
            void* ptr = this->getObjectFromIndexInPage(index);
            *((void**)ptr) = this->freelist;

            this->freelist = ptr;
            this->freecount++;
        }

        constexpr std::pair<AtomicGCMetadata*, void*> gcLoadFreeNext() 
        {
            if(this->freelist == nullptr) {
                return {nullptr, META_FREE_LIST_OOM_SENTINAL};
            }
            else {
                void* next = this->freelist;
                this->freelist = *((void**)next);

                return {getMetadataForObj(next), next};
            }
        }

        static PageInfo* setPageMetaData(void* vpp, GCAllocatorImpl* gcalloc, std::thread::id threadid);
        void* reset();

        void rebuild();
    };

    constexpr GCAllocatorImpl* gcGetAllocator(void* ptr)
    {
        return PageInfo::extractPageFromPointer(ptr)->gcalloc;
    }

    constexpr const TypeInfo* gcGetTypeInfo(void* ptr)
    {
        return PageInfo::extractPageFromPointer(ptr)->typeinfo;
    }

    inline std::thread::id gcGetThreadId(void* ptr)
    {
        return PageInfo::extractPageFromPointer(ptr)->threadid;
    }

    constexpr AtomicGCMetadata* gcGetMetadata(void* ptr)
    {
        return PageInfo::getMetadataForObj(ptr);
    }

    class GCAllocatorImpl
    {
    private:
        std::pair<AtomicGCMetadata*, void*> nextalloc;
        PageInfo* allocpage; // Page in which we are currently allocating from
         
        std::pair<AtomicGCMetadata*, void*> nextevac;
        PageInfo* evacpage; // Page in which we are currently evacuating from

    private:
        std::list<PageInfo*> filled_pages; // Pages which we have young allocated into and pending processing
        std::list<PageInfo*> hot_nursery_pages; // Pages which we have evacuated into and pending processing
        std::list<PageInfo*> pageset; //All pages allocated by this allocator that are not currently being allocated from or in the filled list

        size_t allocatedbytes;

        PageInfo* allocatorNurseryPageFinder(double availthreshold);
        PageInfo* allocatorGeneralPageFinder(double availthreshold);
        void allocatorSlowPathRefresh();
        void evacuatorSlowPathRefresh();

    public:
        const TypeInfo* alloctype; 

        GCAllocatorImpl(const TypeInfo* alloctype) : nextalloc{nullptr, META_FREE_LIST_OOM_SENTINAL}, allocpage{}, nextevac{nullptr, META_FREE_LIST_OOM_SENTINAL}, evacpage{}, filled_pages{}, hot_nursery_pages{}, pageset{}, allocatedbytes{0}, alloctype{alloctype} { ; }

        constexpr void* xalloc()
        {
            GC_METRICS_BASIC_OP(g_memstats.processalloc(this->alloctype->bytesize));

            if(this->nextalloc.second == META_FREE_LIST_OOM_SENTINAL) [[unlikely]] { 
                this->allocatorSlowPathRefresh();
            }
        
            auto [meta, ptr] = this->nextalloc;
            this->nextalloc = this->allocpage->gcLoadFreeNext();
            gcInitOnAllocate(meta);

            return ptr;
        }

        inline void* xalloc_evac(void** parentslotptr)
        {
            if(this->nextevac.second == META_FREE_LIST_OOM_SENTINAL) [[unlikely]] { 
                this->evacuatorSlowPathRefresh();
            }
        
            auto [meta, ptr] = this->nextevac;
            this->nextevac = this->evacpage->gcLoadFreeNext();
            gcInitOnEvacuate(meta, parentslotptr);

            return ptr;
        }

        inline void xrcRelease(void* ptr)
        {
            AtomicGCMetadata* meta = gcGetMetadata(ptr);
            gcProcessSweep(meta);
        }

        void processNursery()
        {
            if(this->allocpage != nullptr) {
                this->filled_pages.push_back(this->allocpage);
                
                this->allocpage = nullptr;
                this->nextalloc = {nullptr, META_FREE_LIST_OOM_SENTINAL};
            }

            //
            //TODO: Here is where we want to route some pages to aged (and thus rotate the heap slowly)
            //      Initial design is just to move some fraction to the aged page set to keep consistent turnover of pages (and this reclaiming memory and identifying free pages for reuse)
            //

#if GC_CLEAR_EAGER_FEATURE
            std::for_each(this->filled_pages.begin(), this->filled_pages.end(), [](PageInfo* pp) { 
                pp->rebuild(); 
            });
#endif
            this->hot_nursery_pages.splice(this->hot_nursery_pages.end(), this->filled_pages);
        }

        void cleanup()
        {
            if(this->allocpage != nullptr) {
                this->filled_pages.push_back(this->allocpage);
                this->allocpage = nullptr;
            }
            if(this->evacpage != nullptr) {
                this->pageset.push_back(this->evacpage);
                this->evacpage = nullptr;
            }

            std::for_each(this->filled_pages.begin(), this->filled_pages.end(), [](PageInfo* pp) { pp->reset(); });
            this->filled_pages.clear();

            std::for_each(this->hot_nursery_pages.begin(), this->hot_nursery_pages.end(), [](PageInfo* pp) { pp->reset(); });
            this->hot_nursery_pages.clear();

            std::for_each(this->pageset.begin(), this->pageset.end(), [](PageInfo* pp) { pp->reset(); });
            this->pageset.clear();
        }
    };

    template <typename T>
    class GCAllocator : public GCAllocatorImpl
    {
    public:
        GCAllocator(const TypeInfo* alloctype) : GCAllocatorImpl(alloctype) {}

        template<typename... Args>
        inline T* allocate(Args... args) 
        {
            return new (this->xalloc()) T{args...};
        }

        template<typename... Args>
        inline T* construct(Args... args) 
        {
            return new (this->xalloc()) T(args...);
        }
    };

    class AllocatorThreadLocalInfo
    {
    public:
        void** native_stack_base; //the base of the native stack
        std::vector<std::pair<AtomicGCMetadata*, void*>> old_roots;

        std::map<uint32_t, GCAllocatorImpl*> gcallocs;
        size_t allocatedbytes;

        void* pendingdelete; //objects pending delete

        void (*procdecsfp)(size_t);
        void (*collectfp)();

        AllocatorThreadLocalInfo() : native_stack_base{}, old_roots{}, gcallocs{}, allocatedbytes{}, pendingdelete{}, procdecsfp{}, collectfp{} { ; }

        void initialize(void** caller_rbp, void(*_procdecsfp)(size_t), void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs);
        void cleanup();
    };

    class AllocatorGlobalInfo
    {
    private:
        //This allows us to only-once process immortal objects
        std::mutex g_globals_mutex;
        void* g_globals;
        void** g_globals_lastproc; //last global entry processed during GC runs
        void** g_globals_end; //the current last initialized global entry

        std::unordered_set<void*> allocatedpages;
        std::vector<void*> emptypages;

    public:
        // This mutex protects all global allocator page operations
        std::mutex g_pages_mutex;

        // This mutex protects RC critical sections (and where our imprecise stack roots could materialize a ref to a RC object)
        std::mutex g_rcops_mutex;
        
        // This mutex protects all global IO buffer allocator operations
        std::mutex g_ioalloc_mutex;

        AllocatorGlobalInfo() : g_globals_mutex{}, g_globals{}, g_globals_lastproc{}, g_globals_end{}, allocatedpages{}, emptypages{}, g_pages_mutex{}, g_rcops_mutex{}, g_ioalloc_mutex{} { ; }

        ////////////////
        //Support for immortal object processing -- will block all other GC threads when new data is processed
        ////////////////
        void initializeGlobalRegion(void* data);
        void* getGlobalRegionStorageOfSize(size_t k);
        bool loadGlobalRootsToProc(std::vector<void*>& possibleroots);
        void unloadGlobalRootsFromProc(bool processed);

        PageInfo* getEmptyPage(GCAllocatorImpl* gcalloc);

        // Check if the address refers into any valid allocation (even in middle of it) and if so get the associated metadata
        bool isAllocatedAddress(void* addr, AtomicGCMetadata*& meta, void*& raddr);

        ////////////////
        //Support for Mint Allocator -- can only be called from mint server thread
        ////////////////

        template<typename T>
        T* mint_alloc()
        {
            constexpr size_t bin = std::bit_ceil(sizeof(T));
            constexpr size_t size2 = (size_t)std::pow(2, bin);
            
            return (T*)malloc(size2);
        }

        template<typename T>
        void mint_free(T* ptr)
        {
            if(ptr == nullptr) {
                return;
            }

            free((void*)ptr);
        }

        uint8_t* mint_alloc_buff(size_t bytes)
        {
            size_t bin = std::bit_ceil(bytes);
            size_t size2 = (size_t)std::pow(2, bin);
            
            return (uint8_t*)malloc(size2);
        }

        void mint_free_buff(uint8_t* ptr)
        {
            if(ptr == nullptr) {
                return;
            }

            free((void*)ptr);
        }

        ////////////////
        //Support for IO Buffer Allocator
        ////////////////

        uint8_t* io_buffer_alloc()
        {
            std::lock_guard<std::mutex> lock(this->g_ioalloc_mutex);

            return (uint8_t*)malloc(MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE);
        }

        void io_buffer_free(uint8_t* ptr)
        {
            if(ptr == nullptr) {
                return;
            }

            std::lock_guard<std::mutex> lock(this->g_ioalloc_mutex);

            free(ptr);
        }

        void io_buffer_free_list(std::list<uint8_t*>& buflist)
        {
            std::lock_guard<std::mutex> lock(this->g_ioalloc_mutex);

            for(auto iter = buflist.begin(); iter != buflist.end(); iter++) {
                free(*iter);
            }

            buflist.clear();
        }   
    };

    extern thread_local AllocatorThreadLocalInfo tl_alloc_info;
    extern AllocatorGlobalInfo g_alloc_info;
}

