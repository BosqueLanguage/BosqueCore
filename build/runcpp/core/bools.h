#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    class XBool
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr XBool() : value(0) {}
        constexpr XBool(uint64_t v) : value(v) {}
        constexpr XBool(const XBool& other) = default;

        constexpr static XBool from(bool b) { return XBool(b ? 1ull : 0ull); }
        constexpr static bool toBool(XBool b) { return b.value != 0ull; }

        friend constexpr bool operator<(const XBool &lhs, const XBool &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XBool &lhs, const XBool &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XBool &lhs, const XBool &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XBool &lhs, const XBool &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XBool &lhs, const XBool &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XBool &lhs, const XBool &rhs) { return !(lhs.value < rhs.value); }
    };

    constexpr TypeInfo g_typeinfo_Bool = {
        WELL_KNOWN_TYPE_ID_BOOL,
        sizeof(XBool),
        byteSizeToSlotCount(sizeof(XBool)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "Bool",
        nullptr
    };
}
