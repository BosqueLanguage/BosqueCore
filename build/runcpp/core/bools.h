#pragma once

#include "../common.h"
#include "../bsqtype.h"

namespace Core 
{
    namespace ᐸRuntimeᐳ
    {
        constexpr TypeInfoBase g_wellKnownTypeBool = {
            WELL_KNOWN_TYPE_ID_BOOL,
            sizeof(Bool),
            byteSizeToSlotCount(sizeof(Bool)),
            LayoutTag::Value,
            BSQ_PTR_MASK_LEAF,
            "Bool",
            nullptr
        };
    }

    class BBool
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr BBool() noexcept : value(0) {}
        constexpr BBool(uint64_t v) noexcept : value(v) {}
        constexpr BBool(const BBool& other) noexcept = default;

        constexpr static BBool from(bool b) noexcept { return BBool(b ? 1ull : 0ull); }
        constexpr static bool toBool(BBool b) noexcept { return b.value != 0ull; }


        friend constexpr bool operator<(const BBool &lhs, const BBool &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const BBool &lhs, const BBool &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const BBool &lhs, const BBool &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const BBool &lhs, const BBool &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const BBool &lhs, const BBool &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const BBool &lhs, const BBool &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    namespace ᐸRuntimeᐳ
    {
        constexpr BBool bfalse = BBool::from(false);
        constexpr BBool btrue = BBool::from(true);
    }
}
