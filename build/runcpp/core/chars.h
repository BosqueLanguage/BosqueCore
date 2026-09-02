#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bools.h"

namespace ᐸRuntimeᐳ 
{
    class XByte
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        friend XBool operator==(const XByte &lhs, const XByte &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XByte &lhs, const XByte &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XByte &lhs, const XByte &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XCChar
    {
    public:
        int64_t value; // Stored as uint64_t for alignment reasons

        friend XBool operator==(const XCChar &lhs, const XCChar &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XCChar &lhs, const XCChar &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XCChar &lhs, const XCChar &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XUnicodeChar
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons
        
        friend XBool operator==(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    inline constexpr TypeInfo g_typeinfo_Byte = {
        WELL_KNOWN_TYPE_ID_BYTE,
        sizeof(XByte),
        byteSizeToSlotCount(sizeof(XByte)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "Byte",
        true
    };

    inline constexpr TypeInfo g_typeinfo_CChar = {
        WELL_KNOWN_TYPE_ID_CCHAR,
        sizeof(XCChar),
        byteSizeToSlotCount(sizeof(XCChar)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "CChar",
        true
    };

    inline constexpr TypeInfo g_typeinfo_UnicodeChar = {
        WELL_KNOWN_TYPE_ID_UNICODECHAR,
        sizeof(XUnicodeChar),
        byteSizeToSlotCount(sizeof(XUnicodeChar)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "UnicodeChar",
        true
    };
}
