#pragma once

#include "../../common.h"

#include "../../core/bsqtype.h"

namespace ᐸRuntimeᐳ
{
    constexpr size_t MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE = 8192; //8KB blocks for buffer allocation

    class AllocatorThreadLocalInfo
    {
    public:
        // Add any allocator specific thread local info here

        ////////////////
        //Support for IO Buffer Allocator and interop with Native code
        ////////////////

        void* io_buffer_alloc()
        {
            return (uint8_t*)malloc(MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE);
        }

        //Pin data of type T in the GC root section -- returns base pointer to pinned data for cleanup
        template <typename T>
        void* pin_gc_root(T v)
        {
            return;
        }

        //Release previously pinned GC root data -- takes the pointer returned from pin_gc_root and zeros it out of the GC root section
        template <typename T>
        void release_gc_root(void* ptr)
        {
            return;
        }
    };

    class AllocatorGlobalInfo
    {
    private:
        // This mutex protects all global allocator page operations
        std::mutex g_pages_mutex;
        
        // This mutex protects all global IO buffer allocator operations
        std::mutex g_ioalloc_mutex;

    public:
        // This mutex ensures that at most one GC thread is performing RC inc/dec operations at any given time -- later if we find high contention we can shard this to per page CAS operations
        std::mutex g_rcop_mutex;

        
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
    };

    extern thread_local AllocatorThreadLocalInfo tl_alloc_info;
    extern AllocatorGlobalInfo g_alloc_info;
}

