#pragma once

#include "memory.h"

namespace ᐸRuntimeᐳ
{
    constexpr size_t MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE = 8192; //8KB blocks for buffer allocation

    void runCollect();

    class GCAllocatorImpl;
    class GCPageList;

    using FreeListEntry = uint64_t;

    ////////////////////////////////////////////
    // Page Layout:
    // | Page Metadata | Objects Metadata | Data |
    class PageInfo
    {
    public:
        const TypeInfo* typeinfo; //all entries are of same type
        GCAllocatorImpl* gcalloc; //alloc for this->typeinfo

        FreeListEntry* freelist; //allocate from here until nullptr
        int64_t freecount;
        int64_t esize; //max number of entries in this page

        void* data; //start of the data block
        GCMetadata* mdata; // Meta data is stored out-of-band
        uint32_t p2size; //power of 2 rounded (slot size) of the type stored in this page
        uint32_t size2shift; //shift bits for power of 2 rounded (slot size) of the type stored in this page

        size_t age; //increment age of this page
        PageInfo* prev;
        PageInfo* next;


	    //RC_ADDR bits in freelist entries are [nextoffset | memoffset] in terms of sizeof(void*) indexing!
        constexpr static uint64_t makeFreeListEntry(uint16_t nextoffset, uint16_t memoffset) {
            return (((uint64_t)nextoffset << 16) | (uint64_t)memoffset) << META_BIT_RC_FREELIST_SHIFT;
        }

        constexpr static uint16_t getNextOffsetFromFreeListEntry(FreeListEntry entry) {
            return (uint16_t)((entry >> META_BIT_RC_FREELIST_SHIFT) >> 16);
        }

        constexpr static uint16_t getMemOffsetFromFreeListEntry(FreeListEntry entry) {
            return (uint16_t)((entry >> META_BIT_RC_FREELIST_SHIFT) & 0xFFFF);
        }

        constexpr static PageInfo* extractPageFromPointer(void* p) {
            return (PageInfo*)((uintptr_t)(p) & GC_PAGE_ADDR_MASK);
        }

        constexpr uint16_t getIndexForObjectInPage(void* obj) { 
            return (uint16_t)(((void**)obj - (void**)this->data) << this->size2shift);
        }

        constexpr void* getObjectFromIndexInPage(size_t idx) {
            return this->data + idx;
        }

        constexpr uint16_t getIndexForMetadataInPage(void* obj) { 
            return (uint16_t)(((void**)obj - (void**)this->data) << this->size2shift);
        }

        constexpr GCMetadata* getMetadataFromIndexInPage(size_t idx) {
            return this->mdata + idx;
        }

        constexpr static GCMetadata* getMetadataForObj(void* obj) {
            PageInfo* page = extractPageFromPointer(obj);
            return page->mdata + page->getIndexForMetadataInPage(obj);
        }

        static PageInfo* setPageMetaData(void* vpp, GCAllocatorImpl* gcalloc, size_t agectr, PageInfo* prev, PageInfo* next));
        static void* reset(PageInfo* pp);

        void rebuild(size_t agectr);
	
	    // TODO we should investiage this and see if we can optimize the work needed to 
	    // compute addr of metadata
        static inline GCMetadata* getObjectMetadataAligned(void* obj) noexcept { 
            PageInfo* page = extractPageFromPointer(obj);
		    size_t idx = PageInfo::getIndexForObjectInPage(obj, page);
        
            return page->getMetaEntryAtIndex(idx);
        }
    };


#if BSQ_ALLOCATOR_USE_MALLOC
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

                GCMetadata* meta = gcGetMetadata((GCMetadata*)ptr);
                gcInitOnAllocate(meta->rc);

                this->nursery[this->allocount++] = ptr;
                return ptr;
            }
            else {
                void* ptr = malloc(this->alloctype->bytesize + sizeof(GCMetadata));
                void* obj = gcInitAllocGCMetadata(ptr, this);

                this->x_allocs.insert(obj);
                GCAllocatorImpl::x_all_alloc_to_allocator_map.insert({obj, this});

                this->nursery[this->allocount++] = obj;
                return obj;
            }
        }

        inline void* xalloc_evac(void** parentslotptr)
        {
            void* ptr = malloc(this->alloctype->bytesize + sizeof(GCMetadata));
            void* obj = gcInitEvacGCMetadata(ptr, this, parentslotptr);

            this->x_allocs.insert(obj);
            GCAllocatorImpl::x_all_alloc_to_allocator_map.insert({obj, this});

            return obj;
        }

        inline void xrcRelease(void* ptr)
        {
            GCMetadata* meta = gcGetMetadata(ptr);
            gcProcessSweep(meta->rc);

            this->x_allocs.erase(ptr);
            GCAllocatorImpl::x_all_alloc_to_allocator_map.erase(ptr);

            free((void*)meta);
        }

        bool checkObjectBounds(void* addr, void* omem, const GCMetadata* meta, void*& raddr)
        {            
            const uintptr_t objstart = (uintptr_t)(omem);
            const uintptr_t objend = objstart + ((GCAllocatorImpl*)meta->allocator)->alloctype->bytesize;
            
            if((objstart <= (uintptr_t)addr) && ((uintptr_t)addr < objend)) {
                raddr = omem;
                return true;
            }

            return false;
        }

        bool isAddrInValidObject(void* addr, GCMetadata*& meta, void*& raddr)
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

        bool isAddrSuitableCategory(const GCMetadata* meta)
        {
            if(!gcIsAllocated(meta->rc)) {
                return false;
            }

            if(gcIsYoung(meta->rc) && meta->threadid != std::this_thread::get_id()) {
                return false;
            }

            return true;
        }

        void processNursery()
        {
            for(size_t i = 0; i < this->allocount; ++i) {
                GCMetadata* meta = gcGetMetadata(this->nursery[i]);
                if(!gcIsAllocated(meta->rc) | gcIsYoung(meta->rc)) {
                    gcProcessSweep(meta->rc);
                    
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
                free((void*)gcGetMetadata(*iter));
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
    class GCAllocatorImpl
    {
    private:
    
    public:
        const TypeInfo* alloctype; 

        GCAllocatorImpl(const TypeInfo* alloctype) : alloctype(alloctype) {} 

        void cleanup()
        {
        }
    };

    template <typename T>
    class GCAllocator : public GCAllocatorImpl
    {
    public:
        GCAllocator(const TypeInfo* alloctype) : GCAllocatorImpl(alloctype) {}

        inline void* xalloc()
        {
            assert(false);
        }

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
        std::thread::id threadid; //the id of the thread this info is associated with

        void** native_stack_base; //the base of the native stack
        std::vector<void*> old_roots;

        std::map<uint32_t, GCAllocatorImpl*> gcallocs;
        //TODO -- should have sparse vector to quickly get alloc for evacuate

        void (*collectfp)();

        MemStats memstats;

        AllocatorThreadLocalInfo() : native_stack_base{}, old_roots{}, gcallocs{}, collectfp{}, memstats{} { ; }

        void initialize(std::thread::id threadid, void** caller_rbp, void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs);
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

    public:
        // This mutex protects all global allocator page operations
        std::mutex g_pages_mutex;

        // This mutex protects RC critical sections (and where our imprecise stack roots could materialize a ref to a RC object)
        std::mutex g_rcops_mutex;
        
        // This mutex protects all global IO buffer allocator operations
        std::mutex g_ioalloc_mutex;

        AllocatorGlobalInfo() : g_globals_mutex{}, g_globals{}, g_globals_lastproc{}, g_globals_end{}, g_pages_mutex{}, g_rcops_mutex{}, g_ioalloc_mutex{} { ; }

        ////////////////
        //Support for immortal object processing -- will block all other GC threads when new data is processed
        ////////////////
        void initializeGlobalRegion(void* data);
        void* getGlobalRegionStorageOfSize(size_t k);
        bool loadGlobalRootsToProc(std::vector<void*>& possibleroots);
        void unloadGlobalRootsFromProc(bool processed);

        // Check if the address refers into any valid allocation (even in middle of it) and if so get the associated metadata
        bool isAllocatedAddress(void* addr, GCMetadata*& meta, void*& raddr);

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

