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

        constexpr static XUUIDv4 nil() { return XUUIDv4{0}; }

        friend constexpr XBool operator==(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin())); }
        friend constexpr XBool operator<(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend())); }
        friend constexpr XBool operator>(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend())); }
        friend constexpr XBool operator!=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin()))); }
        friend constexpr XBool operator<=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend()))); }
        friend constexpr XBool operator>=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return XBool::from(!(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend()))); }
    };

    class XUUIDv7
    {
    public:
         std::array<uint8_t, 16> value;

        constexpr static XUUIDv7 nil() { return XUUIDv7{0}; }

        friend constexpr XBool operator==(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin())); }
        friend constexpr XBool operator<(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend())); }
        friend constexpr XBool operator>(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend())); }
        friend constexpr XBool operator!=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin()))); }
        friend constexpr XBool operator<=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend()))); }
        friend constexpr XBool operator>=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return XBool::from(!(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend()))); }
    };

    inline constexpr TypeInfo g_typeinfo_UUIDv4 = {
        WELL_KNOWN_TYPE_ID_UUIDV4,
        sizeof(XUUIDv4),
        byteSizeToSlotCount(sizeof(XUUIDv4)),
        LayoutTag::Value,
        BSQ_TYPEINFO_NO_ESLOT,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "UUIDv4"
    };

    inline constexpr TypeInfo g_typeinfo_UUIDv7 = {
        WELL_KNOWN_TYPE_ID_UUIDV7,
        sizeof(XUUIDv7),
        byteSizeToSlotCount(sizeof(XUUIDv7)),
        LayoutTag::Value,
        BSQ_TYPEINFO_NO_ESLOT,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "UUIDv7"
    };
}
