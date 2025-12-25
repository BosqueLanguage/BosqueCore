#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ 
{
    class XByte
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        friend constexpr bool operator<(const XByte &lhs, const XByte &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XByte &lhs, const XByte &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XByte &lhs, const XByte &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XByte &lhs, const XByte &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XByte &lhs, const XByte &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XByte &lhs, const XByte &rhs) { return !(lhs.value < rhs.value); }
    };

    class XCChar
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        friend constexpr bool operator<(const XCChar &lhs, const XCChar &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XCChar &lhs, const XCChar &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XCChar &lhs, const XCChar &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XCChar &lhs, const XCChar &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XCChar &lhs, const XCChar &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XCChar &lhs, const XCChar &rhs) { return !(lhs.value < rhs.value); }
    };

    class XUnicodeChar
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        friend constexpr bool operator<(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return !(lhs.value < rhs.value); }
    };
}
