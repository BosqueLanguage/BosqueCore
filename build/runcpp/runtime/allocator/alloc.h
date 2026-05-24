#pragma once

#include "memory.h"

namespace ᐸRuntimeᐳ
{
    constexpr size_t MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE = 8192; //8KB blocks for buffer allocation

#if BSQ_ALLOCATOR_USE_MALLOC
    class GCAllocatorImpl
    {
    private:
        std::vector<void*> x_allocs;

    public:
        const TypeInfo* alloctype; 

        constexpr GCAllocatorImpl(const TypeInfo* alloctype) : alloctype(alloctype) {} 

        template<typename T>
        inline void* xalloc()
        {
            void* ptr = malloc(this->alloctype->bytesize + sizeof(GCMetadata));

            this->x_allocs.push_back(ptr);
            return gcInitAllocGCMetadata(ptr, this->alloctype);
        }

        void cleanup()
        {
            for(size_t i = 0; i < this->x_allocs.size(); i++) {
                free(this->x_allocs[i]);
            }

            this->x_allocs.clear();
        }
    };

    template <typename T>
    class GCAllocator : public GCAllocatorImpl
    {
    public:
        constexpr GCAllocator(const TypeInfo* alloctype) : GCAllocatorImpl(alloctype) {}

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

        constexpr GCAllocatorImpl(const TypeInfo* alloctype) : alloctype(alloctype) {} 

        void cleanup()
        {
        }
    };

    template <typename T>
    class GCAllocator : public GCAllocatorImpl
    {
    public:
        constexpr GCAllocator(const TypeInfo* alloctype) : GCAllocatorImpl(alloctype) {}

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
        thread:: threadid; //the id of the thread this info is associated with

        void** native_stack_base; //the base of the native stack
        std::vector<void*> old_roots;

        std::map<uint32_t, GCAllocatorImpl*> gcallocs;
        //TODO -- should have sparse vector to quickly get alloc for evacuate

        void (*collectfp)();

        MemStats memstats;

        AllocatorThreadLocalInfo() : native_stack_base{}, old_roots{}, gcallocs{}, collectfp{}, memstats{} { ; }

        void initialize(void** caller_rbp, void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs);
        void cleanup();
    };

    class AllocatorGlobalInfo
    {
    private:
        //This allows us to only-once process immortal objects
        std::mutex g_globals_mutex;
        void** g_globals_lastproc; //last global entry processed during GC runs
        void** g_globals_end; //the current last initialized global entry

    public:
        // This mutex protects all global allocator page operations
        std::mutex g_pages_mutex;
        
        // This mutex protects all global IO buffer allocator operations
        std::mutex g_ioalloc_mutex;

        AllocatorGlobalInfo() : g_globals_mutex{}, g_globals_lastproc{}, g_globals_end{}, g_pages_mutex{}, g_ioalloc_mutex{} { ; }

        ////////////////
        //Support for immortal object processing -- will block all other GC threads when new data is processed
        ////////////////
        bool loadGlobalRootsToProc(std::vector<void*>& possibleroots);
        void unloadGlobalRootsFromProc(bool processed);

        // Check if the address refers into any valid allocation (even in middle of it) and if so get the associated metadata
        bool isAllocatedAddress(void* addr, GCMetadata& m);

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

