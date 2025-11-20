#pragma once

#include "../common.h"

namespace Core 
{
    class Byte
    {
    private:
        uint64_t value; // Stored as uint64_t for alignment reasons

    public:
        constexpr Byte() noexcept : value(0) {}
        constexpr Byte(uint64_t v) noexcept : value(v) {}
        constexpr Byte(const Byte& other) noexcept = default;
        constexpr Byte(Byte&& other) noexcept = default;
        ~Byte() noexcept = default;

        constexpr Byte& operator=(const Byte& other) noexcept = default;
        constexpr Byte& operator=(Byte&& other) noexcept = default;

        friend inline constexpr bool operator<(const Byte &lhs, const Byte &rhs) noexcept { return lhs.value < rhs.value; }
        friend inline constexpr bool operator==(const Byte &lhs, const Byte &rhs) noexcept { return lhs.value == rhs.value; }
        friend inline constexpr bool operator>(const Byte &lhs, const Byte &rhs) noexcept { return rhs.value < lhs.value; }
        friend inline constexpr bool operator!=(const Byte &lhs, const Byte &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend inline constexpr bool operator<=(const Byte &lhs, const Byte &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend inline constexpr bool operator>=(const Byte &lhs, const Byte &rhs) noexcept { return !(lhs.value < rhs.value); }
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
        constexpr CChar(CChar&& other) noexcept = default;
        ~CChar() noexcept = default;

        constexpr CChar& operator=(const CChar& other) noexcept = default;
        constexpr CChar& operator=(CChar&& other) noexcept = default;

        friend inline constexpr bool operator<(const CChar &lhs, const CChar &rhs) noexcept { return lhs.value < rhs.value; }
        friend inline constexpr bool operator==(const CChar &lhs, const CChar &rhs) noexcept { return lhs.value == rhs.value; }
        friend inline constexpr bool operator>(const CChar &lhs, const CChar &rhs) noexcept { return rhs.value < lhs.value; }
        friend inline constexpr bool operator!=(const CChar &lhs, const CChar &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend inline constexpr bool operator<=(const CChar &lhs, const CChar &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend inline constexpr bool operator>=(const CChar &lhs, const CChar &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class UnicodeChar
    {
    private:
        uint64_t value; // Stored as uint32_t for alignment reasons

    public:
        constexpr UnicodeChar() noexcept : value(0) {}
        constexpr UnicodeChar(uint64_t v) noexcept : value(v) {}
        constexpr UnicodeChar(char v) noexcept : value((uint64_t)v) {}
        constexpr UnicodeChar(const UnicodeChar& other) noexcept = default;
        constexpr UnicodeChar(UnicodeChar&& other) noexcept = default;
        ~UnicodeChar() noexcept = default;

        constexpr UnicodeChar& operator=(const UnicodeChar& other) noexcept = default;
        constexpr UnicodeChar& operator=(UnicodeChar&& other) noexcept = default;

        friend inline constexpr bool operator<(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return lhs.value < rhs.value; }
        friend inline constexpr bool operator==(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return lhs.value == rhs.value; }
        friend inline constexpr bool operator>(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return rhs.value < lhs.value; }
        friend inline constexpr bool operator!=(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend inline constexpr bool operator<=(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend inline constexpr bool operator>=(const UnicodeChar &lhs, const UnicodeChar &rhs) noexcept { return !(lhs.value < rhs.value); }
    };
}
