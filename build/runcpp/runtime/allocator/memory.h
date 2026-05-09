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
    constexpr size_t GC_METADATA_OFFSET = (sizeof(GCMetadata) / sizeof(void*));;
    static_assert(GC_METADATA_SIZE == 16, "GCMetadata size must be a multiple of max alignment");

    constexpr GCMetadata* getMetadata(void* ptr)
    {
        return reinterpret_cast<GCMetadata*>(ptr - GC_METADATA_OFFSET);
    }

    constexpr const TypeInfo* getTypeInfo(void* ptr)
    {
        return getMetadata(ptr)->typeinfo;
    }

    constexpr void* initAllocGCMetadata(void* ptr, const TypeInfo* typeinfo)
    {
        GCMetadata* meta = getMetadata(ptr);
        meta->typeinfo = typeinfo;
        meta->isalloc = 1;
        meta->isyoung = 1;
        meta->ismarked = 0;
        meta->isrootref = 0;
        meta->rc = 0;

        return ptr + GC_METADATA_OFFSET;
    }
#else
#endif //BSQ_ALLOCATOR_USE_MALLOC
}
