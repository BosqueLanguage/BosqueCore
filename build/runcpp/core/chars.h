#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ 
{
    class XByte
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr XByte() : value(0) {}
        constexpr XByte(uint64_t v) : value(v) {}
        constexpr XByte(uint8_t v) : value((uint64_t)v) {}
        constexpr XByte(const XByte& other) = default;

        uint8_t getValue() const { return (uint8_t)(this->value); }

        friend constexpr bool operator<(const XByte &lhs, const XByte &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XByte &lhs, const XByte &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XByte &lhs, const XByte &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XByte &lhs, const XByte &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XByte &lhs, const XByte &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XByte &lhs, const XByte &rhs) { return !(lhs.value < rhs.value); }
    };

    class XCChar
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr XCChar() : value(0) {}
        constexpr XCChar(uint64_t v) : value(v) {}
        constexpr XCChar(char v) : value((uint64_t)v) {}
        constexpr XCChar(const XCChar& other) = default;

        char getValue() const { return (char)(this->value); }

        friend constexpr bool operator<(const XCChar &lhs, const XCChar &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XCChar &lhs, const XCChar &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XCChar &lhs, const XCChar &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XCChar &lhs, const XCChar &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XCChar &lhs, const XCChar &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XCChar &lhs, const XCChar &rhs) { return !(lhs.value < rhs.value); }
    };

    class XUnicodeChar
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr XUnicodeChar() : value(0) {}
        constexpr XUnicodeChar(uint64_t v) : value(v) {}
        constexpr XUnicodeChar(char v) : value((uint64_t)v) {}
        constexpr XUnicodeChar(const XUnicodeChar& other) = default;

        uint64_t getValue() const { return this->value; }

        friend constexpr bool operator<(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XUnicodeChar &lhs, const XUnicodeChar &rhs) { return !(lhs.value < rhs.value); }
    };
}
