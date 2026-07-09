#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bools.h"

namespace ᐸRuntimeᐳ
{
    class XUUIDv4
    {
    public:
        std::array<uint8_t, 16> value;

        static XUUIDv4 nil() { return XUUIDv4{}; }

        friend XBool operator==(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin())); }
        friend XBool operator<(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend())); }
        friend XBool operator>(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend())); }
        friend XBool operator!=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin()))); }
        friend XBool operator<=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend()))); }
        friend XBool operator>=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend()))); }
    };

    class XUUIDv7
    {
    public:
        std::array<uint8_t, 16> value;

        static XUUIDv7 nil() { return XUUIDv7{}; }

        friend XBool operator==(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin())); }
        friend XBool operator<(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend())); }
        friend XBool operator>(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend())); }
        friend XBool operator!=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin()))); }
        friend XBool operator<=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend()))); }
        friend XBool operator>=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend()))); }
    };

    inline constexpr TypeInfo g_typeinfo_UUIDv4 = {
        WELL_KNOWN_TYPE_ID_UUIDV4,
        sizeof(XUUIDv4),
        byteSizeToSlotCount(sizeof(XUUIDv4)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "UUIDv4",
        true
    };

    inline constexpr TypeInfo g_typeinfo_UUIDv7 = {
        WELL_KNOWN_TYPE_ID_UUIDV7,
        sizeof(XUUIDv7),
        byteSizeToSlotCount(sizeof(XUUIDv7)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "UUIDv7",
        true
    };
}
