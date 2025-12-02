#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ 
{
    class Byte
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr Byte() : value(0) {}
        constexpr Byte(uint64_t v) : value(v) {}
        constexpr Byte(uint8_t v) : value((uint64_t)v) {}
        constexpr Byte(const Byte& other) = default;

        uint8_t getValue() const { return (uint8_t)(this->value); }

        friend constexpr bool operator<(const Byte &lhs, const Byte &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const Byte &lhs, const Byte &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const Byte &lhs, const Byte &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const Byte &lhs, const Byte &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const Byte &lhs, const Byte &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const Byte &lhs, const Byte &rhs) { return !(lhs.value < rhs.value); }
    };

    class CChar
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr CChar() : value(0) {}
        constexpr CChar(uint64_t v) : value(v) {}
        constexpr CChar(char v) : value((uint64_t)v) {}
        constexpr CChar(const CChar& other) = default;

        char getValue() const { return (char)(this->value); }

        friend constexpr bool operator<(const CChar &lhs, const CChar &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const CChar &lhs, const CChar &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const CChar &lhs, const CChar &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const CChar &lhs, const CChar &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const CChar &lhs, const CChar &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const CChar &lhs, const CChar &rhs) { return !(lhs.value < rhs.value); }
    };

    class UnicodeChar
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr UnicodeChar() : value(0) {}
        constexpr UnicodeChar(uint64_t v) : value(v) {}
        constexpr UnicodeChar(char v) : value((uint64_t)v) {}
        constexpr UnicodeChar(const UnicodeChar& other) = default;

        uint64_t getValue() const { return this->value; }

        friend constexpr bool operator<(const UnicodeChar &lhs, const UnicodeChar &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const UnicodeChar &lhs, const UnicodeChar &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const UnicodeChar &lhs, const UnicodeChar &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const UnicodeChar &lhs, const UnicodeChar &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const UnicodeChar &lhs, const UnicodeChar &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const UnicodeChar &lhs, const UnicodeChar &rhs) { return !(lhs.value < rhs.value); }
    };
}
