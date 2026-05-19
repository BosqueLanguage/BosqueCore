#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    class XBool
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        constexpr static XBool from(bool b) { return XBool{(uint64_t)b}; }

        constexpr explicit inline operator bool() const { return (bool)this->value; }

        friend constexpr inline XBool operator!(const XBool &b) { return XBool{b.value ^ 1}; }
        friend constexpr inline XBool operator&(const XBool &lhs, const XBool &rhs) { return XBool{lhs.value & rhs.value}; }
        friend constexpr inline XBool operator|(const XBool &lhs, const XBool &rhs) { return XBool{lhs.value | rhs.value}; }

        friend constexpr inline XBool operator==(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value == rhs.value)}; }
        friend constexpr inline XBool operator<(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value < rhs.value)}; }
        friend constexpr inline XBool operator>(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value > rhs.value)}; }
        friend constexpr inline XBool operator!=(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value != rhs.value)}; }
        friend constexpr inline XBool operator<=(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value <= rhs.value)}; }
        friend constexpr inline XBool operator>=(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value >= rhs.value)}; }
    };

    constexpr XBool XFALSE = XBool{0};
    constexpr XBool XTRUE = XBool{1};

    inline constexpr TypeInfo g_typeinfo_Bool = {
        WELL_KNOWN_TYPE_ID_BOOL,
        sizeof(XBool),
        byteSizeToSlotCount(sizeof(XBool)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "Bool"
    };
}
