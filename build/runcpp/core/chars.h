#pragma once

#include "../common.h"

namespace ᐸRuntimeᐳ 
{
    class Byte
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr Byte() noexcept : value(0) {}
        constexpr Byte(uint64_t v) noexcept : value(v) {}
        constexpr Byte(uint8_t v) noexcept : value((uint64_t)v) {}
        constexpr Byte(const Byte& other) noexcept = default;

        friend constexpr bool operator<(const Byte &lhs, const Byte &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const Byte &lhs, const Byte &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const Byte &lhs, const Byte &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const Byte &lhs, const Byte &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const Byte &lhs, const Byte &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const Byte &lhs, const Byte &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class CChar
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr CChar() noexcept : value(0) {}
        constexpr CChar(uint64_t v) noexcept : value(v) {}
        constexpr CChar(char v) noexcept : value((uint64_t)v) {}
        constexpr CChar(const CChar& other) noexcept = default;

        friend constexpr bool operator<(const CChar &lhs, const CChar &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const CChar &lhs, const CChar &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const CChar &lhs, const CChar &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const CChar &lhs, const CChar &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const CChar &lhs, const CChar &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const CChar &lhs, const CChar &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class UnicodeChar
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr UnicodeChar() noexcept : value(0) {}
        constexpr UnicodeChar(uint64_t v) noexcept : value(v) {}
        constexpr UnicodeChar(char v) noexcept : value((uint64_t)v) {}
        constexpr UnicodeChar(const UnicodeChar& other) noexcept = default;

        friend constexpr bool operator<(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return !(lhs.value < rhs.value); }
    };
}
