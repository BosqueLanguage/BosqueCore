#pragma once

#include "../common.h"

namespace Core 
{
    class Nat
    {
    public:
        static constexpr int64_t MAX_NAT = BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 

    private:
        int64_t value;

        inline constexpr static bool isValidNat(int64_t v) noexcept
        {
            return (0 <= v) & (v <= Nat::MAX_NAT);
        }

    public:
        constexpr Nat() noexcept : value(0) {}
        constexpr Nat(int64_t v) noexcept : value(v) {}
        constexpr Nat(const Nat& other) noexcept = default;
        constexpr Nat(Nat&& other) noexcept = default;
        ~Nat() noexcept = default;

        constexpr Nat& operator=(const Nat& other) noexcept = default;
        constexpr Nat& operator=(Nat&& other) noexcept = default;

        // Overloaded operators on Nat
        
        inline constexpr Nat operator+() const noexcept
        {
            return Nat{this->value};
        }
        // Negation is not defined for Nat

        friend inline constexpr Nat operator+(Nat lhs, Nat rhs) noexcept
        {
            int64_t result = 0;
            if(__builtin_add_overflow(lhs.value, rhs.value, &result) || !Nat::isValidNat(result)) { BSQ_ABORT; }
            return Nat{result};
        }
        friend inline constexpr Nat operator-(Nat lhs, Nat rhs) noexcept
        {
            int64_t result = 0;
            if(__builtin_sub_overflow(lhs.value, rhs.value, &result) || !Nat::isValidNat(result)) { BSQ_ABORT; }
            return Nat{result};
        }
        friend inline constexpr Nat operator/(Nat lhs, Nat rhs) noexcept
        {
            if(rhs.value == 0) { BSQ_ABORT; }
            return Nat{lhs.value / rhs.value};
        }
        friend inline constexpr Nat operator*(Nat lhs, Nat rhs) noexcept
        {
            int64_t result = 0;
            if(__builtin_mul_overflow(lhs.value, rhs.value, &result) || !Nat::isValidNat(result)) { BSQ_ABORT; }
            return Nat{result};
        }

        friend inline constexpr bool operator<(const Nat &lhs, const Nat &rhs) noexcept { return lhs.value < rhs.value; }
        friend inline constexpr bool operator==(const Nat &lhs, const Nat &rhs) noexcept { return lhs.value == rhs.value; }
        friend inline constexpr bool operator>(const Nat &lhs, const Nat &rhs) noexcept { return rhs < lhs; }
        friend inline constexpr bool operator!=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs == rhs); }
        friend inline constexpr bool operator<=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs > rhs); }
        friend inline constexpr bool operator>=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs < rhs); }
    };

    class Int
    {
    public:
        static constexpr int64_t MIN_INT = -BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 
        static constexpr int64_t MAX_INT = BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 

    private:
        int64_t value;

        inline constexpr static bool isValidInt(int64_t v) noexcept
        {
            return (MIN_INT <= v) & (v <= MAX_INT);
        }

    public:
        constexpr Int() noexcept : value(0) {}
        constexpr Int(int64_t v) noexcept : value(v) {}
        constexpr Int(const Int& other) noexcept = default;
        constexpr Int(Int&& other) noexcept = default;
        ~Int() noexcept = default;

        constexpr Int& operator=(const Int& other) noexcept = default;
        constexpr Int& operator=(Int&& other) noexcept = default;

        // Overloaded operators on Int
        
        inline constexpr Int operator+() const noexcept
        {
            return Int{this->value};
        }
        inline constexpr Int operator-() const noexcept
        {
            return Int{-this->value};
        }

        friend inline constexpr Int operator+(Int lhs, Int rhs) noexcept
        {
            int64_t result = 0;
            if(__builtin_add_overflow(lhs.value, rhs.value, &result) || !Int::isValidInt(result)) { BSQ_ABORT; }
            return Int{result};
        }
        friend inline constexpr Int operator-(Int lhs, Int rhs) noexcept
        {
            int64_t result = 0;
            if(__builtin_sub_overflow(lhs.value, rhs.value, &result) || !Int::isValidInt(result)) { BSQ_ABORT; }
            return Int{result};
        }
        friend inline constexpr Int operator/(Int lhs, Int rhs) noexcept
        {
            if(rhs.value == 0) { BSQ_ABORT; }
            return Int{lhs.value / rhs.value};
        }
        friend inline constexpr Int operator*(Int lhs, Int rhs) noexcept
        {
            int64_t result = 0;
            if(__builtin_mul_overflow(lhs.value, rhs.value, &result) || !Int::isValidInt(result)) { BSQ_ABORT; }
            return Int{result};
        }

        friend inline constexpr bool operator<(const Int &lhs, const Int &rhs) noexcept { return lhs.value < rhs.value; }
        friend inline constexpr bool operator==(const Int &lhs, const Int &rhs) noexcept { return lhs.value == rhs.value; }
        friend inline constexpr bool operator>(const Int &lhs, const Int &rhs) noexcept { return rhs < lhs; }
        friend inline constexpr bool operator!=(const Int &lhs, const Int &rhs) noexcept { return !(lhs == rhs); }
        friend inline constexpr bool operator<=(const Int &lhs, const Int &rhs) noexcept { return !(lhs > rhs); }
        friend inline constexpr bool operator>=(const Int &lhs, const Int &rhs) noexcept { return !(lhs < rhs); }
    };

    class BigNat
    {
    public:
    };

    class BigInt
    {
    public:
    };

    inline constexpr Nat operator""_Nat(unsigned long long n)
    {
        return Nat{n};
    }
}
