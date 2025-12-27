#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bools.h"

namespace ᐸRuntimeᐳ 
{
    class XByte
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        friend constexpr XBool operator==(const XByte &lhs, const XByte &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend constexpr XBool operator<(const XByte &lhs, const XByte &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend constexpr XBool operator>(const XByte &lhs, const XByte &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend constexpr XBool operator!=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend constexpr XBool operator<=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend constexpr XBool operator>=(const XByte &lhs, const XByte &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XCChar
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        friend constexpr XBool operator==(const XCChar &lhs, const XCChar &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend constexpr XBool operator<(const XCChar &lhs, const XCChar &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend constexpr XBool operator>(const XCChar &lhs, const XCChar &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend constexpr XBool operator!=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend constexpr XBool operator<=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend constexpr XBool operator>=(const XCChar &lhs, const XCChar &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XUnicodeChar
    {
    public:
        uint64_t value; // Stored as uint64_t for alignment reasons

        friend constexpr XBool operator==(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend constexpr XBool operator<(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend constexpr XBool operator>(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend constexpr XBool operator!=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend constexpr XBool operator<=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend constexpr XBool operator>=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };
}
