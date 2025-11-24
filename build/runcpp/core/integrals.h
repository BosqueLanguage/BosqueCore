#pragma once

#include "../common.h"

namespace Core 
{
    class Nat
    {
    public:
        static constexpr int64_t MAX_NAT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE;

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

        // Check operators on Nat
        inline static void checkOverflowAddition(Nat n1, Nat n2, const char* file, uint32_t line) noexcept
        {
            int64_t result = 0;
            if(!__builtin_add_overflow_p(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat addition bounds"); }
        }
        inline static void checkOverflowSubtraction(Nat n1, Nat n2, const char* file, uint32_t line) noexcept
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Nat subtraction underflow"); }
            int64_t result = 0;
            if(!__builtin_sub_overflow(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(Nat n1, Nat n2, const char* file, uint32_t line) noexcept
        {
            int64_t result = 0;
            if(!__builtin_mul_overflow(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat multiplication bounds"); }
        }
        inline static void checkDivisionByZero(Nat n2, const char* file, uint32_t line) noexcept
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Nat division by zero"); }
        }

        // Overloaded operators on Nat
        constexpr Nat operator+() const noexcept
        {
            return Nat(this->value);
        }
        // Negation is not defined for Nat

        friend constexpr Nat operator+(Nat lhs, Nat rhs) noexcept
        {
            return Nat(lhs.value + rhs.value);
        }
        friend constexpr Nat operator-(Nat lhs, Nat rhs) noexcept
        {
            return Nat(lhs.value - rhs.value);
        }
        friend constexpr Nat operator/(Nat lhs, Nat rhs) noexcept
        {
           return Nat(lhs.value / rhs.value);
        }
        friend constexpr Nat operator*(Nat lhs, Nat rhs) noexcept
        {
            return Nat(lhs.value * rhs.value);
        }

        friend constexpr bool operator<(const Nat &lhs, const Nat &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const Nat &lhs, const Nat &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const Nat &lhs, const Nat &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const Nat &lhs, const Nat &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class Int
    {
    public:
        static constexpr int64_t MIN_INT = -ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 
        static constexpr int64_t MAX_INT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 

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

        // Check operators on Int
        inline static void checkOverflowAddition(Int n1, Int n2, const char* file, uint32_t line) noexcept
        {
            int64_t result = 0;
            if(!__builtin_add_overflow_p(n1.value, n2.value, &result) || !(Int::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int addition bounds"); }
        }
        inline static void checkOverflowSubtraction(Int n1, Int n2, const char* file, uint32_t line) noexcept
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Int subtraction underflow"); }
            int64_t result = 0;
            if(!__builtin_sub_overflow(n1.value, n2.value, &result) || !(Int::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(Int n1, Int n2, const char* file, uint32_t line) noexcept
        {
            int64_t result = 0;
            if(!__builtin_mul_overflow(n1.value, n2.value, &result) || !(Int::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int multiplication bounds"); }
        }
        inline static void checkDivisionByZero(Int n2, const char* file, uint32_t line) noexcept
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Int
        constexpr Int operator+() const noexcept
        {
            return Int(this->value);
        }
        constexpr Int operator-() const noexcept
        {
            return Int(-this->value);
        }

        friend constexpr Int operator+(Int lhs, Int rhs) noexcept
        {
            return Int(lhs.value + rhs.value);
        }
        friend constexpr Int operator-(Int lhs, Int rhs) noexcept
        {
            return Int(lhs.value - rhs.value);
        }
        friend constexpr Int operator/(Int lhs, Int rhs) noexcept
        {
            return Int(lhs.value / rhs.value);
        }
        friend constexpr Int operator*(Int lhs, Int rhs) noexcept
        {
            return Int(lhs.value * rhs.value);
        }

        friend constexpr bool operator<(const Int &lhs, const Int &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const Int &lhs, const Int &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const Int &lhs, const Int &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const Int &lhs, const Int &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const Int &lhs, const Int &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const Int &lhs, const Int &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class SafeNat
    {
    public:
        static constexpr __int128_t MAX_NAT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        inline constexpr static bool isValidNat(__int128_t v) noexcept
        {
            return (0 <= v) & (v <= SafeNat::MAX_NAT);
        }

    private:
        __int128_t value;

        static constexpr __int128_t BOTTOM_VALUE = (__int128_t(1) << 126);

        inline constexpr static bool s_isBottom(__int128_t v) noexcept
        {
            return (v & BOTTOM_VALUE) != 0;
        }

    public:
        constexpr SafeNat() noexcept : value(0) {}
        constexpr SafeNat(__int128_t v) noexcept : value(v) {}
        constexpr SafeNat(const SafeNat& other) noexcept = default;

        constexpr bool isBottom() const noexcept
        {
            return SafeNat::s_isBottom(this->value);
        }

        // Overloaded operators on Nat
        constexpr SafeNat operator+() const noexcept
        {
            return SafeNat(this->value);
        }
        // Negation is not defined for Nat

        friend constexpr SafeNat operator+(SafeNat lhs, SafeNat rhs) noexcept
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return SafeNat(SafeNat::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_add_overflow_p(lhs.value, rhs.value, &result) && (SafeNat::isValidNat(result))) [[likely]] {
                return SafeNat(result);
            }
            else {
                return SafeNat(SafeNat::BOTTOM_VALUE);
            }
        }
        friend constexpr SafeNat operator-(SafeNat lhs, SafeNat rhs) noexcept
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return SafeNat(SafeNat::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if((rhs.value <= lhs.value) && !__builtin_sub_overflow(lhs.value, rhs.value, &result) && (SafeNat::isValidNat(result))) [[likely]] {
                return SafeNat(result);
            }
            else {
                return SafeNat(SafeNat::BOTTOM_VALUE);
            }
        }
        friend constexpr SafeNat operator/(SafeNat lhs, SafeNat rhs) noexcept
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return SafeNat(SafeNat::BOTTOM_VALUE);
            }

            if(rhs.value != 0) [[likely]] {
                return SafeNat(lhs.value / rhs.value);
            }
            else {
                return SafeNat(SafeNat::BOTTOM_VALUE);
            }
        }
        friend constexpr SafeNat operator*(SafeNat lhs, SafeNat rhs) noexcept
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return SafeNat(SafeNat::BOTTOM_VALUE);
            }

           __int128_t result = 0;
            if(!__builtin_mul_overflow(lhs.value, rhs.value, &result) && (SafeNat::isValidNat(result))) [[likely]] {
                return SafeNat(result);
            }
            else {
                return SafeNat(SafeNat::BOTTOM_VALUE);
            }
        }

        friend constexpr bool operator<(const SafeNat &lhs, const SafeNat &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const SafeNat &lhs, const SafeNat &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const SafeNat &lhs, const SafeNat &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const SafeNat &lhs, const SafeNat &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const SafeNat &lhs, const SafeNat &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const SafeNat &lhs, const SafeNat &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class BigInt
    {
    public:
        static constexpr __int128_t MIN_INT = -ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 
        static constexpr __int128_t MAX_INT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        inline constexpr static bool isValidInt(__int128_t v) noexcept
        {
            return (BigInt::MIN_INT <= v) & (v <= BigInt::MAX_INT);
        }

    private:
        __int128_t value;
        
        static constexpr __int128_t BOTTOM_VALUE = (__int128_t(1) << 126);

        inline constexpr static bool isBottom(__int128_t v) noexcept
        {
            return (v & BOTTOM_VALUE) != 0;
        }

    public:

    //TODO: need pos and neg bottom to keep ordering reasonable (like a - b goes to neg if b > a or a neg and b pos etc)
        constexpr BigInt() noexcept : value(0) {}
        constexpr BigInt(__int128_t v) noexcept : value(v) {}
        constexpr BigInt(const BigInt& other) noexcept = default;

        constexpr bool isBottom() const noexcept
        {
            return BigInt::isBottom(this->value);
        }

        // Overloaded operators on Int
        constexpr BigInt operator+() const noexcept
        {
            return BigInt(this->value);
        }
        constexpr BigInt operator-() const noexcept
        {
            return BigInt(-this->value);
        }

        friend constexpr BigInt operator+(BigInt lhs, BigInt rhs) noexcept
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return BigInt(BigInt::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_add_overflow_p(lhs.value, rhs.value, &result) && (BigInt::isValidInt(result))) [[likely]] {
                return BigInt(result);
            }
            else {
                return BigInt(BigInt::BOTTOM_VALUE);
            }
        }
        friend constexpr BigInt operator-(BigInt lhs, BigInt rhs) noexcept
        {
            //figure out what way to overflow
        }
    };

    constexpr Nat operator""_Nat(unsigned long long n)
    {
        return Nat(n);
    }

    constexpr Int operator""_Int(unsigned long long n)
    {
        return Int(n);
    }

    static_assert(sizeof(Nat) == sizeof(int64_t), "Nat size incorrect");
    static_assert(sizeof(Int) == sizeof(int64_t), "Int size incorrect");
    static_assert(sizeof(SafeNat) == sizeof(__int128_t), "BigNat size incorrect");
    static_assert(sizeof(SafeInt) == sizeof(__int128_t), "BigInt size incorrect");
}
