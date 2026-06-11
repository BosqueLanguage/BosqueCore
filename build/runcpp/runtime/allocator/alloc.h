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

        uint16_t freelistidx; //allocate from here until OOM sentinal is hit
        int64_t freecount;
        int64_t esize; //max number of entries in this page

        void* data; //start of the data block
        AtomicGCMetadata* mdata; // Meta data is stored out-of-band
        uint32_t p2size; //power of 2 rounded (slot size) of the type stored in this page
        uint32_t size2shift; //shift bits for power of 2 rounded (slot size) of the type stored in this page

        size_t age; //increment age of this page
    
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

        static PageInfo* setPageMetaData(void* vpp, GCAllocatorImpl* gcalloc, std::thread::id threadid, size_t agectr);
        static void* reset(PageInfo* pp);

        void rebuild(size_t agectr);
    };


#if BSQ_ALLOCATOR_USE_MALLOC
    struct GCMetadataMalloc
    {
        GCAllocatorImpl* allocator;
        std::thread::id threadid;
        AtomicGCMetadata rc;
    };

    void runCollect();

    constexpr size_t GC_METADATA_SIZE = sizeof(GCMetadataMalloc);
    static_assert(GC_METADATA_SIZE == 24, "GCMetadata size must be a multiple of max alignment");

    constexpr GCMetadataMalloc* gcGetMetadataMalloc(void* ptr)
    {
        return (GCMetadataMalloc*)(((uint8_t*)ptr) - GC_METADATA_SIZE);
    }

    constexpr GCAllocatorImpl* gcGetAllocator(void* ptr)
    {
        return gcGetMetadataMalloc(ptr)->allocator;
    }

    constexpr const TypeInfo* gcGetTypeInfo(void* ptr)
    {
        return *((const TypeInfo**)gcGetMetadataMalloc(ptr)->allocator);
    }

    inline std::thread::id gcGetThreadId(void* ptr)
    {
        return gcGetMetadataMalloc(ptr)->threadid;
    }

    constexpr AtomicGCMetadata* gcGetMetadata(void* ptr)
    {
        return &(((GCMetadataMalloc*)(((uint8_t*)ptr) - GC_METADATA_SIZE))->rc);
    }

    constexpr void* gcInitAllocGCMetadata(void* ptr, GCAllocatorImpl* allocator)
    {
        GCMetadataMalloc* meta = (GCMetadataMalloc*)ptr;
        meta->allocator = allocator;
        meta->threadid = std::this_thread::get_id();
        gcInitOnAllocate(&(meta->rc));

        return (void*)((uint8_t*)ptr + GC_METADATA_SIZE);
    }

    constexpr void* gcInitEvacGCMetadata(void* ptr, GCAllocatorImpl* allocator, void** parentslotptr)
    {
        GCMetadataMalloc* meta = (GCMetadataMalloc*)ptr;
        meta->allocator = allocator;
        meta->threadid = std::this_thread::get_id();
        gcInitOnEvacuate(&(meta->rc), parentslotptr);

        return (void*)((uint8_t*)ptr + GC_METADATA_SIZE);
    }

    class GCAllocatorImpl
    {
    public:
        constexpr static size_t NURSERY_SIZE = GC_NURSERY_SIZE;

        const TypeInfo* alloctype;
        void* freelist;
        void* pendingdelete;


        std::array<void*, NURSERY_SIZE> nursery;
        size_t allocount;

        std::set<void*> x_allocs;
        static std::map<void*, GCAllocatorImpl*> x_all_alloc_to_allocator_map;

        GCAllocatorImpl(const TypeInfo* alloctype) : alloctype{alloctype}, freelist{nullptr}, pendingdelete{nullptr}, nursery{}, allocount(0), x_allocs{} { ; } 

        inline void* xalloc()
        {
            if(this->allocount >= NURSERY_SIZE) {
                runCollect();
            }

            if(this->freelist != nullptr) {
                void* ptr = this->freelist;
                this->freelist = *((void**)ptr);

                AtomicGCMetadata* meta = gcGetMetadata(ptr);
                gcInitOnAllocate(meta);

                this->nursery[this->allocount++] = ptr;
                return ptr;
            }
            else {
                void* ptr = malloc(this->alloctype->bytesize + sizeof(GCMetadataMalloc));
                void* obj = gcInitAllocGCMetadata(ptr, this);

                this->x_allocs.insert(obj);
                GCAllocatorImpl::x_all_alloc_to_allocator_map.insert({obj, this});

                this->nursery[this->allocount++] = obj;
                return obj;
            }
        }

        inline void* xalloc_evac(void** parentslotptr)
        {
            void* ptr = malloc(this->alloctype->bytesize + sizeof(GCMetadataMalloc));
            void* obj = gcInitEvacGCMetadata(ptr, this, parentslotptr);

            this->x_allocs.insert(obj);
            GCAllocatorImpl::x_all_alloc_to_allocator_map.insert({obj, this});

            return obj;
        }

        inline void xrcRelease(void* ptr)
        {
            AtomicGCMetadata* meta = gcGetMetadata(ptr);
            gcProcessSweep(meta);

            this->x_allocs.erase(ptr);
            GCAllocatorImpl::x_all_alloc_to_allocator_map.erase(ptr);

            free((void*)((uint8_t*)ptr - GC_METADATA_SIZE));
        }

        bool checkObjectBounds(void* addr, void* omem, const AtomicGCMetadata* meta, void*& raddr)
        {            
            const uintptr_t objstart = (uintptr_t)(omem);
            const uintptr_t objend = objstart + this->alloctype->bytesize;
            
            if((objstart <= (uintptr_t)addr) && ((uintptr_t)addr < objend)) {
                raddr = omem;
                return true;
            }

            return false;
        }

        bool isAddrInValidObject(void* addr, AtomicGCMetadata*& meta, void*& raddr)
        {
            if(this->x_allocs.empty()) {
                return false;
            }

            auto iter = this->x_allocs.lower_bound(addr);
            if(iter != this->x_allocs.begin() && *iter != addr) {
                iter--;
            }
            
            meta = gcGetMetadata(*iter);
            return this->checkObjectBounds(addr, *iter, meta, raddr);
        }

        bool isAddrSuitableCategory(const AtomicGCMetadata* meta, void* raddr)
        {
            if(!gcIsAllocated(meta)) {
                return false;
            }

            std::thread::id objtid = gcGetThreadId(raddr);
            if(gcIsYoung(meta) && objtid != std::this_thread::get_id()) {
                return false;
            }

            return true;
        }

        void processNursery()
        {
            for(size_t i = 0; i < this->allocount; ++i) {
                AtomicGCMetadata* meta = gcGetMetadata(this->nursery[i]);
                if(!gcIsAllocated(meta) | gcIsYoung(meta)) {
                    gcProcessSweep(meta);
                    
                    *((void**)this->nursery[i]) = this->freelist;
                    this->freelist = this->nursery[i];
                }
                
                this->nursery[i] = nullptr;
            }

            this->allocount = 0;
        }

        void cleanup()
        {
            for(auto iter = this->x_allocs.begin(); iter != this->x_allocs.end(); iter++) {
                free((void*)((uint8_t*)*iter - GC_METADATA_SIZE));
            }

            this->x_allocs.clear();
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
#else
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

    struct PageAgeCmp 
    { 
        bool operator()(PageInfo* a, PageInfo* b) const {
            return a->age < b->age;
        }
    };

    class GCAllocatorImpl
    {
    private:
        uint16_t freelistidx;
        uint16_t evaclistidx;

        PageInfo* allocpage; // Page in which we are currently allocating from
        PageInfo* evacpage; // Page in which we are currently evacuating from

    public:
        void* pendingdelete;

    private:
        std::vector<PageInfo*> filled_pages; // Pages which we have young allocated into and pending processing
        std::multiset<PageInfo*, PageAgeCmp> pageset; //All pages allocated by this allocator that are not currently being allocated from or in the filled list -- ordered by age

        size_t agectr;
        size_t allocatedbytes;

        PageInfo* allocatorPageFinder(double availthreshold, size_t age);
        void allocatorSlowPathRefresh();
        void evacuatorSlowPathRefresh();

    public:
        const TypeInfo* alloctype; 

        GCAllocatorImpl(const TypeInfo* alloctype) : freelistidx{META_FREE_LIST_OOM_SENTINAL}, evaclistidx{META_FREE_LIST_OOM_SENTINAL}, allocpage{}, evacpage{}, pendingdelete{}, filled_pages{}, pageset{}, agectr{1}, allocatedbytes{0}, alloctype{alloctype} { ; }

        constexpr size_t generateNextAge() 
        {
            return this->agectr++;
        }

        constexpr void* xalloc()
        {
            if(this->freelistidx == META_FREE_LIST_OOM_SENTINAL) [[unlikely]] { 
                this->allocatorSlowPathRefresh();
            }
        
            uint16_t freeidx = this->freelistidx;
            AtomicGCMetadata* meta = this->allocpage->getMetadataFromIndexInPage(freeidx);

            this->freelistidx = gcLoadFreeListNext(meta);
            gcInitOnAllocate(meta);

            return this->allocpage->getObjectFromIndexInPage(freeidx);
        }

        inline void* xalloc_evac(void** parentslotptr)
        {
            if(this->evaclistidx == META_FREE_LIST_OOM_SENTINAL) [[unlikely]] { 
                this->evacuatorSlowPathRefresh();
            }
        
            uint16_t evacidx = this->evaclistidx;
            AtomicGCMetadata* meta = this->allocpage->getMetadataFromIndexInPage(evacidx);

            this->evaclistidx = gcLoadFreeListNext(meta);
            gcInitOnEvacuate(meta, parentslotptr);

            return this->allocpage->getObjectFromIndexInPage(evacidx);
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
                this->freelistidx = META_FREE_LIST_OOM_SENTINAL;
            }

            //
            //TODO: Here is where we want to route some pages to aged (and thus rotate the heap slowly)
            //      Initial design is just to move some fraction to the aged page set to keep consistent turnover of pages (and this reclaiming memory and identifying free pages for reuse)
            //

            this->pageset.insert(this->filled_pages.begin(), this->filled_pages.end());
            this->filled_pages.clear();
        }

        void cleanup()
        {
            //We are just outa here!!!
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
#endif //BSQ_ALLOCATOR_USE_MALLOC

    class AllocatorThreadLocalInfo
    {
    public:
        void** native_stack_base; //the base of the native stack
        std::vector<std::pair<AtomicGCMetadata*, void*>> old_roots;

        std::map<uint32_t, GCAllocatorImpl*> gcallocs;
        size_t allocatedbytes;

        void (*collectfp)();

        MemStats memstats;

        AllocatorThreadLocalInfo() : native_stack_base{}, old_roots{}, gcallocs{}, allocatedbytes{}, collectfp{}, memstats{} { ; }

        void initialize(void** caller_rbp, void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs);
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

