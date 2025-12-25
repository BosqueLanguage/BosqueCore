#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    class XUUIDv4
    {
    public:
        std::array<uint8_t, 16> value;

        constexpr static XUUIDv4 nil() { return XUUIDv4{0}; }

        friend constexpr bool operator<(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend()); }
        friend constexpr bool operator==(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin()); }
        friend constexpr bool operator>(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend()); }
        friend constexpr bool operator!=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return !(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin())); }
        friend constexpr bool operator<=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return !(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend())); }
        friend constexpr bool operator>=(const XUUIDv4 &lhs, const XUUIDv4 &rhs) { return !(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend())); }
    };

    class XUUIDv7
    {
    public:
         std::array<uint8_t, 16> value;

        constexpr static XUUIDv7 nil() { return XUUIDv7{0}; }

        friend constexpr bool operator<(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend()); }
        friend constexpr bool operator==(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin()); }
        friend constexpr bool operator>(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend()); }
        friend constexpr bool operator!=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return !(std::equal(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin())); }
        friend constexpr bool operator<=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return !(std::lexicographical_compare(lhs.value.cbegin(), lhs.value.cend(), rhs.value.cbegin(), rhs.value.cend())); }
        friend constexpr bool operator>=(const XUUIDv7 &lhs, const XUUIDv7 &rhs) { return !(std::lexicographical_compare(rhs.value.cbegin(), rhs.value.cend(), lhs.value.cbegin(), lhs.value.cend())); }
    };
}
