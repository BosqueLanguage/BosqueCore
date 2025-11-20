#pragma once

#include "../common.h"

namespace Core 
{
    class Nat
    {
    public:
        static constexpr int64_t MAX_NAT = BSQ_NUMERIC_DYNAMIC_RANGE_BASE;

        inline constexpr static bool isValidNat(int64_t v) noexcept
        {
            return (0 <= v) & (v <= Nat::MAX_NAT);
        }

    private:
        int64_t value;

    public:
        constexpr Nat() noexcept : value(0) {}
        constexpr Nat(int64_t v) noexcept : value(v) {}
        constexpr Nat(const Nat& other) noexcept = default;
        constexpr Nat(Nat&& other) noexcept = default;
        ~Nat() noexcept = default;

        constexpr Nat& operator=(const Nat& other) noexcept = default;
        constexpr Nat& operator=(Nat&& other) noexcept = default;

        // Check operators on Nat
        inline static void checkOverflowAddition(Nat n1, Nat n2, const char* file, uint32_t line) noexcept
        {
            int64_t result = 0;
            if(!__builtin_add_overflow_p(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat addition bounds"); }
        }
        inline static void checkOverflowSubtraction(Nat n1, Nat n2, const char* file, uint32_t line) noexcept
        {
            if(n2.value > n1.value) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Nat subtraction underflow"); }

            int64_t result = 0;
            if(!__builtin_sub_overflow(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(Nat n1, Nat n2, const char* file, uint32_t line) noexcept
        {
            int64_t result = 0;
            if(!__builtin_mul_overflow(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat multiplication bounds"); }
        }
        inline static void checkDivisionByZero(Nat n2, const char* file, uint32_t line) noexcept
        {
            if(n2.value == 0) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Nat division by zero"); }
        }

        // Overloaded operators on Nat
        inline constexpr Nat operator+() const noexcept
        {
            return Nat{this->value};
        }
        // Negation is not defined for Nat

        friend inline constexpr Nat operator+(Nat lhs, Nat rhs) noexcept
        {
            return Nat{lhs.value + rhs.value};
        }
        friend inline constexpr Nat operator-(Nat lhs, Nat rhs) noexcept
        {
            return Nat{lhs.value - rhs.value};
        }
        friend inline constexpr Nat operator/(Nat lhs, Nat rhs) noexcept
        {
           return Nat{lhs.value / rhs.value};
        }
        friend inline constexpr Nat operator*(Nat lhs, Nat rhs) noexcept
        {
            return Nat{lhs.value * rhs.value};
        }

        friend inline constexpr bool operator<(const Nat &lhs, const Nat &rhs) noexcept { return lhs.value < rhs.value; }
        friend inline constexpr bool operator==(const Nat &lhs, const Nat &rhs) noexcept { return lhs.value == rhs.value; }
        friend inline constexpr bool operator>(const Nat &lhs, const Nat &rhs) noexcept { return rhs.value < lhs.value; }
        friend inline constexpr bool operator!=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend inline constexpr bool operator<=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend inline constexpr bool operator>=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class Int
    {
    public:
        static constexpr int64_t MIN_INT = -BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 
        static constexpr int64_t MAX_INT = BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 

        inline constexpr static bool isValidInt(int64_t v) noexcept
        {
            return (Int::MIN_INT <= v) & (v <= Int::MAX_INT);
        }

    private:
        int64_t value;

    public:
        constexpr Int() noexcept : value(0) {}
        constexpr Int(int64_t v) noexcept : value(v) {}
        constexpr Int(const Int& other) noexcept = default;
        constexpr Int(Int&& other) noexcept = default;
        ~Int() noexcept = default;

        constexpr Int& operator=(const Int& other) noexcept = default;
        constexpr Int& operator=(Int&& other) noexcept = default;

        // Check operators on Int
        inline static void checkOverflowAddition(Int n1, Int n2, const char* file, uint32_t line) noexcept
        {
            int64_t result = 0;
            if(!__builtin_add_overflow_p(n1.value, n2.value, &result) || !(Int::isValidInt(result))) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int addition bounds"); }
        }
        inline static void checkOverflowSubtraction(Int n1, Int n2, const char* file, uint32_t line) noexcept
        {
            if(n2.value > n1.value) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Int subtraction underflow"); }
            int64_t result = 0;
            if(!__builtin_sub_overflow(n1.value, n2.value, &result) || !(Int::isValidInt(result))) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(Int n1, Int n2, const char* file, uint32_t line) noexcept
        {
            int64_t result = 0;
            if(!__builtin_mul_overflow(n1.value, n2.value, &result) || !(Int::isValidInt(result))) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int multiplication bounds"); }
        }
        inline static void checkDivisionByZero(Int n2, const char* file, uint32_t line) noexcept
        {
            if(n2.value == 0) { BSQ_HANDLE_ERROR(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

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
            return Int{lhs.value + rhs.value};
        }
        friend inline constexpr Int operator-(Int lhs, Int rhs) noexcept
        {
            return Int{lhs.value - rhs.value};
        }
        friend inline constexpr Int operator/(Int lhs, Int rhs) noexcept
        {
            return Int{lhs.value / rhs.value};
        }
        friend inline constexpr Int operator*(Int lhs, Int rhs) noexcept
        {
            return Int{lhs.value * rhs.value};
        }

        friend inline constexpr bool operator<(const Int &lhs, const Int &rhs) noexcept { return lhs.value < rhs.value; }
        friend inline constexpr bool operator==(const Int &lhs, const Int &rhs) noexcept { return lhs.value == rhs.value; }
        friend inline constexpr bool operator>(const Int &lhs, const Int &rhs) noexcept { return rhs.value < lhs.value; }
        friend inline constexpr bool operator!=(const Int &lhs, const Int &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend inline constexpr bool operator<=(const Int &lhs, const Int &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend inline constexpr bool operator>=(const Int &lhs, const Int &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class BigNat
    {
    public:
        static constexpr __int128_t MAX_NAT = BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        inline constexpr static bool isValidNat(__int128_t v) noexcept
        {
            return (0 <= v) & (v <= BigNat::MAX_NAT);
        }

    private:
        __int128_t value;

    public:
    };

    class BigInt
    {
    public:
        static constexpr __int128_t MIN_INT = -BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 
        static constexpr __int128_t MAX_INT = BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        inline constexpr static bool isValidInt(__int128_t v) noexcept
        {
            return (BigInt::MIN_INT <= v) & (v <= BigInt::MAX_INT);
        }

    private:
        __int128_t value;
        
    public:
    };

    inline constexpr Nat operator""_Nat(unsigned long long n)
    {
        return Nat{n};
    }

    inline constexpr Int operator""_Int(unsigned long long n)
    {
        return Int{n};
    }

    static_assert(sizeof(Nat) == sizeof(int64_t), "Nat size incorrect");
    static_assert(sizeof(Int) == sizeof(int64_t), "Int size incorrect");
    static_assert(sizeof(BigNat) == sizeof(__int128_t), "BigNat size incorrect");
    static_assert(sizeof(BigInt) == sizeof(__int128_t), "BigInt size incorrect");
}
