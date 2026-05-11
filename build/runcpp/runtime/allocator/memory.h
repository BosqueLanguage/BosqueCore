#pragma once

#include "../../common.h"
#include "../../core/bsqtype.h"

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
        GCMetadata* meta = gcGetMetadata(ptr);
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
}
