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
    using AtomicMetaBits = std::atomic<uint64_t>;

    constexpr uint64_t META_BIT_IS_ALLOC = 0x1;
    constexpr uint64_t META_BIT_IS_YOUNG = 0x2;
    constexpr uint32_t META_BIT_RC_SHIFT = 3;

    constexpr uint64_t META_BIT_RC_ZERO = 0x0;
    constexpr uint64_t META_BIT_RC_ONE = 0x4;

    constexpr bool gcIsAllocated(const AtomicMetaBits& rc) {
        return (rc.load() & META_BIT_IS_ALLOC) != 0;
    }

    constexpr bool gcIsYoung(const AtomicMetaBits& rc) {
        return (rc.load() & META_BIT_IS_YOUNG) != 0;
    }

    constexpr void gcInitOnAllocate(AtomicMetaBits& rc)
    {
        rc.store(META_BIT_IS_ALLOC | META_BIT_IS_YOUNG);
    }

    constexpr void gcInitOnPromote(AtomicMetaBits& rc)
    {
        rc.store(META_BIT_RC_ONE | META_BIT_IS_ALLOC);
    }

    constexpr void gcIncRefCountConservative(AtomicMetaBits& rc)
    {
        //Make sure we don't do anything strange to a "forged pointer"
        //TOCTOU issue is resolved by a Read-Writer when we have thread shared root ref objects detected

        uint64_t vv = rc.load();
        if((vv & META_BIT_IS_ALLOC) & !(vv & META_BIT_IS_YOUNG) & (vv >= META_BIT_RC_ONE)) {
            rc.fetch_add(META_BIT_RC_ONE);
        }
    }

    constexpr void gcIncRefCountPrecise(AtomicMetaBits& rc)
    {
        rc.fetch_add(META_BIT_RC_ONE);
    }

    constexpr bool gcDecRefCount(AtomicMetaBits& rc)
    {
        return (META_BIT_RC_ZERO | META_BIT_IS_ALLOC) == rc.fetch_sub(META_BIT_RC_ONE);
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
        gcInitOnPromote(meta->rc);

        return (void*)((uint8_t*)ptr + GC_METADATA_SIZE);
    }

    constexpr void promoteYoungInPlace(GCMetadata* meta)
    {
        gcInitOnPromote(meta->rc);
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
