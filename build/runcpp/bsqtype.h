#pragma once

#include "common.h"

#define BSQ_SLOT_BYTE_SIZE 8

#define PTR_MASK_NOP ('0')
#define PTR_MASK_PTR ('1')
#define PTR_MASK_TAGGED ('2')

#define PTR_MASK_LEAF nullptr

#define WELL_KNOWN_TYPE_ID_NONE 0
#define WELL_KNOWN_TYPE_ID_BOOL 1

#define WELL_KNOWN_TYPE_ID_CSTRBUFF 2
#define WELL_KNOWN_TYPE_ID_CSTRNODE 3
#define WELL_KNOWN_TYPE_ID_CSTRING 4

namespace Core
{
    namespace ᐸRuntimeᐳ
    {
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

        constexpr TypeInfoBase g_wellKnownTypeNone = {
            WELL_KNOWN_TYPE_ID_NONE,
            8,
            1,
            LayoutTag::Value,
            PTR_MASK_LEAF,
            "None",
            nullptr
        };

        constexpr TypeInfoBase g_wellKnownTypeBool = {
            WELL_KNOWN_TYPE_ID_BOOL,
            8,
            1,
            LayoutTag::Value,
            PTR_MASK_LEAF,
            "Bool",
            nullptr
        };
    }
}
