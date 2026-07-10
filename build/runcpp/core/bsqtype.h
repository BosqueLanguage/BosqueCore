#pragma once

#include "../common.h"

#define BSQ_PTR_MASK_LEAF nullptr

namespace ᐸRuntimeᐳ
{
    enum class RColor : uint16_t
    {
        Red,
        Black
    };
    
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_NONE = 0;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BOOL = 1;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_INT = 2;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_NAT = 3;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CHKINT = 4;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CHKNAT = 5;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_FLOAT = 6;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_CSTRING = 7;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_CSTRING = 8;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_CSTRING = 9;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING_INLINE = 10;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING_TREE = 11;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CSTRING = 12;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_STRING = 13;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_STRING = 14;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_POSRB_TREE_STRING = 15;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING_INLINE = 16;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING_TREE = 17;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_STRING = 18;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFERENTRY = 19;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFERBLOCK = 20;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_BYTEBUFFER = 21;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_UUIDV4 = 22;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_UUIDV7 = 23;

    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_CREGEX = 24;
    inline constexpr uint32_t WELL_KNOWN_TYPE_ID_REGEX = 25;

    enum class LayoutTag : uint16_t
    {
        Value,     //an inline value
        Ref        //a pointer to a heap allocated value
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
        
        const char* ptrmask; // NULL is for leaf values or structs

        const uint32_t* supertypes;
        const uint32_t supertypescount;
        const FieldOffsetInfo* ftable;
        const uint32_t ftablecount;
        const VInvokeTargetInfo* vitable;
        const uint32_t vitablecount;

        const char* typekey;

        bool quickrelease;
    };

    consteval uint32_t byteSizeToSlotCount(size_t bytesize)
    {
        return bytesize / sizeof(uint64_t);
    }

    consteval uint32_t slotCountToByteSize(size_t slotcount)
    {
        return slotcount * sizeof(uint64_t);
    }

    inline constexpr uint16_t BSQ_TYPEINFO_NO_ESLOT = 0x0;

    inline constexpr TypeInfo g_typeinfo_None = {
        WELL_KNOWN_TYPE_ID_NONE,
        8,
        byteSizeToSlotCount(8),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "None",
        true
    };
}
