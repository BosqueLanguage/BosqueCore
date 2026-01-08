#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    class XBool
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        constexpr static XBool from(bool b) { return XBool{b ? 1ull : 0ull}; }
        constexpr static bool toBool(XBool b) { return (b.value != 0ull); }

        constexpr explicit operator bool() const { return this->value != 0ull; }

        friend constexpr XBool operator!(const XBool &b) { return XBool::from(!XBool::toBool(b)); }
        friend constexpr XBool operator&(const XBool &lhs, const XBool &rhs) { return XBool::from(lhs.value & rhs.value); }
        friend constexpr XBool operator|(const XBool &lhs, const XBool &rhs) { return XBool::from(lhs.value | rhs.value); }

        friend constexpr XBool operator==(const XBool &lhs, const XBool &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend constexpr XBool operator<(const XBool &lhs, const XBool &rhs) { return (!lhs) & rhs; }
        friend constexpr XBool operator>(const XBool &lhs, const XBool &rhs) { return rhs & (!lhs); }
        friend constexpr XBool operator!=(const XBool &lhs, const XBool &rhs) { return !(lhs == rhs); }
        friend constexpr XBool operator<=(const XBool &lhs, const XBool &rhs) { return !(lhs > rhs); }
        friend constexpr XBool operator>=(const XBool &lhs, const XBool &rhs) { return !(lhs < rhs); }
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
