#pragma once

#include "../../common.h"
#include "../../core/bsqtype.h"

#include "memstats.h"

//Make sure any allocated page is addressable by us -- larger than 2^31 and less than 2^42
#define GC_MIN_ALLOCATED_ADDRESS ((void*)(2147483648ul))
#define GC_MAX_ALLOCATED_ADDRESS ((void*)(281474976710656ul))

#define GC_MEM_ALIGNMENT 8

//Control for page sizes and access
#define GC_BITS_IN_ADDR_FOR_PAGE 13ul
#define GC_BLOCK_ALLOCATION_SIZE (1ul << GC_BITS_IN_ADDR_FOR_PAGE)
#define GC_PAGE_MASK ((1ul << GC_BITS_IN_ADDR_FOR_PAGE) - 1ul)
#define GC_PAGE_ADDR_MASK (~GC_PAGE_MASK)

namespace ᐸRuntimeᐳ
{
    using MetaBits = uint64_t;
    using AtomicMetaBits = std::atomic<MetaBits>;

    constexpr MetaBits META_BIT_IS_ALLOC = 0x1;
    constexpr MetaBits META_BIT_IS_YOUNG = 0x2;
    constexpr MetaBits META_BIT_IS_FORWARD = 0x4;

    constexpr MetaBits META_BIT_RC_ZERO = 0x0;
    constexpr MetaBits META_BIT_RC_ONE = 0x8;
    constexpr MetaBits META_BIT_RC_MASK = ~(0x7);

    constexpr bool gcIsAllocated(const AtomicMetaBits& rc) {
        return (rc.load(std::memory_order_relaxed) & META_BIT_IS_ALLOC) != 0;
    }

    constexpr bool gcIsYoung(const AtomicMetaBits& rc) {
        return (rc.load(std::memory_order_relaxed) & META_BIT_IS_YOUNG) != 0;
    }

    constexpr bool gcIsForwarded(const AtomicMetaBits& rc) {
        return (rc.load(std::memory_order_relaxed) & META_BIT_IS_FORWARD) != 0;
    }

    constexpr bool gcIsZeroRefCount(const AtomicMetaBits& rc) {
        return (rc.load(std::memory_order_relaxed) & META_BIT_RC_MASK) != 0;
    }

    constexpr void gcInitOnAllocate(AtomicMetaBits& rc)
    {
        rc.store(META_BIT_IS_ALLOC | META_BIT_IS_YOUNG, std::memory_order_relaxed);
    }

    constexpr void gcInitOnEvacuate(AtomicMetaBits& rc)
    {
        rc.store(META_BIT_IS_ALLOC | META_BIT_RC_ZERO, std::memory_order_relaxed);
    }

    constexpr bool gcRootProcessRCIncrement(AtomicMetaBits& rc)
    {
        //on root increment this could be a "forged" reference 
        //so we CAS to make sure we aren't incrementing a 0 count, young, or unallocated object
        //we hold page mutex so we know the memory location is otherwise valid
        //return true if we successfully incremented, false if this is a TOCTOU or forged reference

        MetaBits ll = rc.load();
        while(true) {
            if(((ll & META_BIT_IS_ALLOC) == 0) | ((ll & META_BIT_IS_YOUNG) != 0) | ((ll & META_BIT_RC_MASK) == META_BIT_RC_ZERO)) {
                return false;
            }

            MetaBits newVal = ll + META_BIT_RC_ONE;
            if(rc.compare_exchange_weak(ll, newVal)) {
                return true;
            }
        }
    }

    constexpr void gcProcessUpdateYoungForward(AtomicMetaBits& rc)
    {
        rc.store(META_BIT_IS_ALLOC | META_BIT_IS_YOUNG | META_BIT_IS_FORWARD, std::memory_order_relaxed);
    }

    constexpr void gcRootProcessYoungPromote(AtomicMetaBits& rc)
    {
        rc.store(META_BIT_IS_ALLOC | META_BIT_RC_ONE, std::memory_order_relaxed);
    }

    constexpr void gcYoungProcessRCIncrement(AtomicMetaBits& rc)
    {
        rc.fetch_add(META_BIT_RC_ONE);
    }

    constexpr bool gcProcessRCDecrement(AtomicMetaBits& rc)
    {
        MetaBits oldVal = rc.fetch_sub(META_BIT_RC_ONE);
        return (oldVal & META_BIT_RC_MASK) == META_BIT_RC_ONE; //was one before decrement, now zero so we want to reclaim
    }

    constexpr void gcProcessSweep(AtomicMetaBits& rc)
    {
        rc.store(0, std::memory_order_relaxed);
    }

#if BSQ_ALLOCATOR_USE_MALLOC
    struct GCMetadata
    {
        void* allocator;
        std::thread::id threadid;
        AtomicMetaBits rc;
    };

    constexpr size_t GC_METADATA_SIZE = sizeof(GCMetadata);
    static_assert(GC_METADATA_SIZE == 24, "GCMetadata size must be a multiple of max alignment");

    constexpr GCMetadata* gcGetMetadata(void* ptr)
    {
        return (GCMetadata*)(((uint8_t*)ptr) - GC_METADATA_SIZE);
    }

    template<typename T>
    constexpr T* gcGetAllocator(void* ptr)
    {
        return *((T**)(((uint8_t*)ptr) - GC_METADATA_SIZE));
    }

    constexpr const TypeInfo* gcGetTypeInfo(void* ptr)
    {
        return **((const TypeInfo***)(((uint8_t*)ptr) - GC_METADATA_SIZE));
    }

    constexpr void* gcInitAllocGCMetadata(void* ptr, void* allocator)
    {
        GCMetadata* meta = (GCMetadata*)ptr;
        meta->allocator = allocator;
        meta->threadid = std::this_thread::get_id();
        gcInitOnAllocate(meta->rc);

        return (void*)((uint8_t*)ptr + GC_METADATA_SIZE);
    }

    constexpr void* gcInitEvacGCMetadata(void* ptr, void* allocator)
    {
        GCMetadata* meta = (GCMetadata*)ptr;
        meta->allocator = allocator;
        meta->threadid = std::this_thread::get_id();
        gcInitOnEvacuate(meta->rc);

        return (void*)((uint8_t*)ptr + GC_METADATA_SIZE);
    }

#else
#endif //BSQ_ALLOCATOR_USE_MALLOC

    struct RegisterContents
    {
        static_assert(__x86_64__, "GC implementation currently only supports x86-64 architecture");

        //Should never have pointers of interest in these
        //void* rbp;
        //void* rsp;

        void* rax = nullptr;
        void* rbx = nullptr;
        void* rcx = nullptr;
        void* rdx = nullptr;
        void* rsi = nullptr;
        void* rdi = nullptr;
        void* r8 = nullptr;
        void* r9 = nullptr;
        void* r10 = nullptr;
        void* r11 = nullptr;
        void* r12 = nullptr;
        void* r13 = nullptr;
        void* r14 = nullptr;
        void* r15 = nullptr;
    };
}
