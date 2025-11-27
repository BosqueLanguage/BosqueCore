#pragma once

#include "../common.h"

namespace ᐸRuntimeᐳ
{
    class UUIDv4
    {
    private:
        char value[16];

    public:
        constexpr UUIDv4() noexcept : value{0} {}
        constexpr UUIDv4(const char v[16]) noexcept : value{0} { std::copy(v, v + 16, value); }
        constexpr UUIDv4(const UUIDv4& other) noexcept = default;

        friend constexpr bool operator<(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return std::lexicographical_compare(lhs.value, lhs.value + 16, rhs.value, rhs.value + 16); }
        friend constexpr bool operator==(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return std::equal(lhs.value, lhs.value + 16, rhs.value); }
        friend constexpr bool operator>(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return std::lexicographical_compare(rhs.value, rhs.value + 16, lhs.value, lhs.value + 16); }
        friend constexpr bool operator!=(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return !(std::equal(lhs.value, lhs.value + 16, rhs.value)); }
        friend constexpr bool operator<=(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return !(std::lexicographical_compare(lhs.value, lhs.value + 16, rhs.value, rhs.value + 16)); }
        friend constexpr bool operator>=(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return !(std::lexicographical_compare(rhs.value, rhs.value + 16, lhs.value, lhs.value + 16)); }
    };

    class UUIDv7
    {
    private:
        char value[16];

    public:
        constexpr UUIDv7() noexcept : value{0} {}
        constexpr UUIDv7(const char v[16]) noexcept : value{0} { std::copy(v, v + 16, value); }
        constexpr UUIDv7(const UUIDv7& other) noexcept = default;

        friend constexpr bool operator<(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return std::lexicographical_compare(lhs.value, lhs.value + 16, rhs.value, rhs.value + 16); }
        friend constexpr bool operator==(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return std::equal(lhs.value, lhs.value + 16, rhs.value); }
        friend constexpr bool operator>(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return std::lexicographical_compare(rhs.value, rhs.value + 16, lhs.value, lhs.value + 16); }
        friend constexpr bool operator!=(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return !(std::equal(lhs.value, lhs.value + 16, rhs.value)); }
        friend constexpr bool operator<=(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return !(std::lexicographical_compare(lhs.value, lhs.value + 16, rhs.value, rhs.value + 16)); }
        friend constexpr bool operator>=(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return !(std::lexicographical_compare(rhs.value, rhs.value + 16, lhs.value, lhs.value + 16)); }
    };
}
