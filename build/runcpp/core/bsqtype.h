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

    constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_CSTRING = 7;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_CSTRING = 8;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING = 9;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING_INLINE = 10;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING_TREE = 11;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING = 12;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_STRING = 13;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_STRING = 14;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING = 15;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING_INLINE = 16;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING_TREE = 17;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING = 18;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFERENTRY = 19;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFERBLOCK = 20;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFER = 21;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_UUIDV4 = 22;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_UUIDV7 = 23;

    constexpr uint32_t WELL_KNOWN_TYPE_ID_CREGEX = 24;
    constexpr uint32_t WELL_KNOWN_TYPE_ID_REGEX = 25;

    enum class LayoutTag : uint16_t
    {
        Value,
        Ref,
        ArrayInline,
        ArrayRef,
        Tagged
    };

    class FieldOffsetInfo
    {
    public:
        uint32_t fieldid;
        uint32_t fieldbsqtypeid;
        uint32_t byteoffset;
        uint32_t slotoffset;

        const char* fieldkey;
        const char* fname;
    };

    using VInvokePtr = void(*)(void);
    class VInvokeTargetInfo
    {
    public:
        uint32_t invokeid;
        VInvokePtr invokeptr;

        const char* invokekey;
    };

    class TypeInfo
    {
    public:
        uint32_t bsqtypeid;
        uint32_t bytesize;
        uint32_t slotcount;
        LayoutTag tag;
        uint16_t slotct; //For array entries this is the number of slots each entry takes (so don't scan more than eslotct * size slots)

        const char* ptrmask; // NULL is for leaf values or structs

        const uint32_t* supertypes;
        const uint32_t supertypescount;
        const FieldOffsetInfo* ftable;
        const uint32_t ftablecount;
        const VInvokeTargetInfo* vitable;
        const uint32_t vitablecount;

        const char* typekey;
    };

    constexpr uint32_t byteSizeToSlotCount(size_t bytesize)
    {
        return bytesize / sizeof(uint64_t);
    }

    constexpr uint32_t slotCountToByteSize(size_t slotcount)
    {
        return slotcount * sizeof(uint64_t);
    }

    constexpr uint16_t BSQ_TYPEINFO_NO_ESLOT = 0x0;

    inline constexpr TypeInfo g_typeinfo_None = {
        WELL_KNOWN_TYPE_ID_NONE,
        8,
        byteSizeToSlotCount(8),
        LayoutTag::Value,
        BSQ_TYPEINFO_NO_ESLOT,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "None"
    };
}
