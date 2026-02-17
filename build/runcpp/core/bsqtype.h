#pragma once

#include "../common.h"

#define BSQ_PTR_MASK_NOP ('0')
#define BSQ_PTR_MASK_PTR ('1')
#define BSQ_PTR_MASK_TAGGED ('2')

#define BSQ_PTR_MASK_LEAF nullptr

namespace ᐸRuntimeᐳ
{
    constexpr uint32_t WELL_KNOWN_TYPE_ID_NONE = 0;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_BOOL = 1;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_INT = 2;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_NAT = 3;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CHKINT = 4;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CHKNAT = 5;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_FLOAT = 6;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTR_TREE_LEAF = 7;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTR_TREE_NODE = 8;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTR_INLINE = 9;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTR_TREE = 10;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING = 11;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_STRBUFF = 12;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_STRNODE = 13;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING = 14;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFERENTRY = 15;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFERBLOCK = 16;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFER = 17;

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

    class TypeInfo
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

    constexpr uint32_t byteSizeToSlotCount(size_t bytesize)
    {
        return bytesize / sizeof(uint64_t);
    }

    constexpr uint32_t slotCountToByteSize(size_t slotcount)
    {
        return slotcount * sizeof(uint64_t);
    }

    constexpr TypeInfo g_typeinfo_None = {
        WELL_KNOWN_TYPE_ID_NONE,
        8,
        byteSizeToSlotCount(8),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "None",
        nullptr
    };
}
