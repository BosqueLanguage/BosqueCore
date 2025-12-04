#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    class BBool
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr BBool() : value(0) {}
        constexpr BBool(uint64_t v) : value(v) {}
        constexpr BBool(const BBool& other) = default;

        constexpr static BBool from(bool b) { return BBool(b ? 1ull : 0ull); }
        constexpr static bool toBool(BBool b) { return b.value != 0ull; }

        friend constexpr bool operator<(const BBool &lhs, const BBool &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const BBool &lhs, const BBool &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const BBool &lhs, const BBool &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const BBool &lhs, const BBool &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const BBool &lhs, const BBool &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const BBool &lhs, const BBool &rhs) { return !(lhs.value < rhs.value); }
    };
    using Bool = BBool; //work around bool kw preventing Class name of Bool

    constexpr TypeInfo g_typeinfo_Bool = {
        WELL_KNOWN_TYPE_ID_BOOL,
        sizeof(Bool),
        byteSizeToSlotCount(sizeof(Bool)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "Bool",
        nullptr
    };
}
