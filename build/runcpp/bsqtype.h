#pragma once

#include "common.h"

#define BSQ_PTR_MASK_NOP ('0')
#define BSQ_PTR_MASK_PTR ('1')
#define BSQ_PTR_MASK_TAGGED ('2')

#define BSQ_PTR_MASK_LEAF nullptr

namespace ᐸRuntimeᐳ
{
    using None = uint64_t;
    constexpr None none = 0ull;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_NONE = 0;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_BOOL = 1;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRBUFF = 2;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRNODE = 3;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING = 4;

    enum class LayoutTag
    {
        Value,
        Ref,
        Tagged
    };

    class FieldOffsetInfo
    {
    public:
        uint32_t fieldid;
        uint32_t fieldbsqtypeid;
        uint32_t byteoffset;
        uint32_t slotoffset;
    };

    class TypeInfoBase
    {
    public:
        uint32_t bsqtypeid;
        uint32_t bytesize;
        uint32_t slotcount;
        LayoutTag tag;

        const char* ptrmask; // NULL is for leaf values or structs
        const char* typekey;
        const FieldOffsetInfo* vtable;
    };

    constexpr uint32_t byteSizeToSlotCount(size_t bytesize) noexcept
    {
        return bytesize / sizeof(uint64_t);
    }

    constexpr uint32_t slotCountToByteSize(size_t slotcount) noexcept
    {
        return slotcount * sizeof(uint64_t);
    }

    constexpr TypeInfoBase g_wellKnownTypeNone = {
        WELL_KNOWN_TYPE_ID_NONE,
        sizeof(None),
        byteSizeToSlotCount(sizeof(None)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "None",
        nullptr
    };
}
