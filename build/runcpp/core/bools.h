#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    class XBool
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        constexpr static inline XBool from(bool b) { return XBool{(uint64_t)b}; }
        constexpr static inline bool toBool(XBool b) { return (bool)b.value; }

        constexpr explicit inline operator bool() const { return this->value != 0ull; }

        friend constexpr inline XBool operator!(const XBool &b) { return XBool{(uint64_t)(!b.value)}; }
        friend constexpr inline XBool operator&(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value & rhs.value)}; }
        friend constexpr inline XBool operator|(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value | rhs.value)}; }

        friend constexpr inline XBool operator==(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value == rhs.value)}; }
        friend constexpr inline XBool operator<(const XBool &lhs, const XBool &rhs) { return (!lhs) & rhs; }
        friend constexpr inline XBool operator>(const XBool &lhs, const XBool &rhs) { return rhs & (!lhs); }
        friend constexpr inline XBool operator!=(const XBool &lhs, const XBool &rhs) { return XBool{(uint64_t)(lhs.value != rhs.value)}; }
        friend constexpr inline XBool operator<=(const XBool &lhs, const XBool &rhs) { return !(lhs > rhs); }
        friend constexpr inline XBool operator>=(const XBool &lhs, const XBool &rhs) { return !(lhs < rhs); }
    };

    constexpr XBool XFALSE = XBool::from(false);
    constexpr XBool XTRUE = XBool::from(true);

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
