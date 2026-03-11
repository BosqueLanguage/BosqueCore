#pragma once

#include "../../common.h"

#include "../../core/bsqtype.h"

namespace ᐸRuntimeᐳ
{
    constexpr size_t MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE = 8192; //8KB blocks for buffer allocation

    class GCAllocatorImpl
    {
    private:
    #if BSQ_ALLOCATOR_USE_MALLOC
        std::vector<void*> x_allocs;
    #endif

    public:
        const TypeInfo* alloctype; 

        constexpr GCAllocatorImpl(const TypeInfo* alloctype) : alloctype(alloctype) {} 

        inline void* xalloc()
        {
    #if BSQ_ALLOCATOR_USE_MALLOC
            void* ptr = malloc(this->alloctype->bytesize);

            this->x_allocs.push_back(ptr);
            return ptr;
    #else 
            assert(false); //Not implemented: GC allocator without malloc
    #endif
        }

        void cleanup()
        {
    #if BSQ_ALLOCATOR_USE_MALLOC
            for(size_t i = 0; i < this->x_allocs.size(); i++) {
                free(this->x_allocs[i]);
            }

            this->x_allocs.clear();
    #endif
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
    };

    class AllocatorThreadLocalInfo
    {
    public:
        std::map<uint32_t, GCAllocatorImpl*> gcallocs;
        void (*collectfp)();

        AllocatorThreadLocalInfo() : gcallocs(), collectfp(nullptr) {}

        void initialize(void** caller_rbp, void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs);
        void cleanup();
    };

    class AllocatorGlobalInfo
    {
    private:
        // This mutex protects all global allocator page operations
        std::mutex g_pages_mutex;
        
        // This mutex protects all global IO buffer allocator operations
        std::mutex g_ioalloc_mutex;

    public:
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

    extern void collect();
}

