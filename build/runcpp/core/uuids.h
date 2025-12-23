#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    class XUUIDv4
    {
    private:
        uint8_t value[16];

    public:
        constexpr XUUIDv4() : value{0} {}
        constexpr XUUIDv4(const uint8_t v[16]) : value{0} { std::copy(v, v + 16, value); }
        constexpr XUUIDv4(const XUUIDv4& other) = default;

        constexpr static XUUIDv4 nil() { return XUUIDv4(); }

        friend constexpr bool operator<(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return std::lexicographical_compare(lhs.value, lhs.value + 16, rhs.value, rhs.value + 16); }
        friend constexpr bool operator==(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return std::equal(lhs.value, lhs.value + 16, rhs.value); }
        friend constexpr bool operator>(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return std::lexicographical_compare(rhs.value, rhs.value + 16, lhs.value, lhs.value + 16); }
        friend constexpr bool operator!=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return !(std::equal(lhs.value, lhs.value + 16, rhs.value)); }
        friend constexpr bool operator<=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return !(std::lexicographical_compare(lhs.value, lhs.value + 16, rhs.value, rhs.value + 16)); }
        friend constexpr bool operator>=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return !(std::lexicographical_compare(rhs.value, rhs.value + 16, lhs.value, lhs.value + 16)); }
    };

    class XUUIDv7
    {
    private:
        uint8_t value[16];

    public:
        constexpr XUUIDv7() : value{0} {}
        constexpr XUUIDv7(const uint8_t v[16]) : value{0} { std::copy(v, v + 16, value); }
        constexpr XUUIDv7(const XUUIDv7& other) = default;

        constexpr static XUUIDv7 nil() { return XUUIDv7(); }

        friend constexpr bool operator<(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return std::lexicographical_compare(lhs.value, lhs.value + 16, rhs.value, rhs.value + 16); }
        friend constexpr bool operator==(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return std::equal(lhs.value, lhs.value + 16, rhs.value); }
        friend constexpr bool operator>(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return std::lexicographical_compare(rhs.value, rhs.value + 16, lhs.value, lhs.value + 16); }
        friend constexpr bool operator!=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return !(std::equal(lhs.value, lhs.value + 16, rhs.value)); }
        friend constexpr bool operator<=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return !(std::lexicographical_compare(lhs.value, lhs.value + 16, rhs.value, rhs.value + 16)); }
        friend constexpr bool operator>=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return !(std::lexicographical_compare(rhs.value, rhs.value + 16, lhs.value, lhs.value + 16)); }
    };
}
