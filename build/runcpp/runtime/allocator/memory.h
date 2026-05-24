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
#if BSQ_ALLOCATOR_USE_MALLOC
    struct GCMetadata
    {
        const TypeInfo* typeinfo;
        uint64_t isalloc    : 1;
        uint64_t isyoung    : 1;
        uint64_t ismarked   : 1;
        uint64_t isrootref  : 1;
        uint64_t rc         : 60; //later tag this for single parent ptr vs counter
    };

    constexpr size_t GC_METADATA_SIZE = sizeof(GCMetadata);
    static_assert(GC_METADATA_SIZE == 16, "GCMetadata size must be a multiple of max alignment");

    constexpr GCMetadata* gcGetMetadata(void* ptr)
    {
        return (GCMetadata*)(((uint8_t*)ptr) - GC_METADATA_SIZE);
    }

    constexpr const TypeInfo* gcGetTypeInfo(void* ptr)
    {
        return gcGetMetadata(ptr)->typeinfo;
    }

    constexpr void* gcInitAllocGCMetadata(void* ptr, const TypeInfo* typeinfo)
    {
        GCMetadata* meta = (GCMetadata*)ptr;
        meta->typeinfo = typeinfo;
        meta->isalloc = 1;
        meta->isyoung = 1;
        meta->ismarked = 0;
        meta->isrootref = 0;
        meta->rc = 0;

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
