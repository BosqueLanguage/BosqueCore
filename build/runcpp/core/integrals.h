#pragma once

#include "../common.h"
#include "../bsqtype.h"

namespace ᐸRuntimeᐳ 
{
    class Nat
    {
    public:
        static constexpr int64_t MAX_NAT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE;

        inline constexpr static bool isValidNat(int64_t v)
        {
            return (0 <= v) & (v <= Nat::MAX_NAT);
        }

    private:
        int64_t value;

    public:
        constexpr Nat() : value(0) {}
        constexpr Nat(int64_t v) : value(v) {}
        constexpr Nat(const Nat& other) = default;

        inline constexpr int64_t getValue() const { return this->value; }

        // Check operators on Nat
        inline static void checkOverflowAddition(Nat n1, Nat n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(!__builtin_add_overflow(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat addition bounds"); }
        }
        inline static void checkOverflowSubtraction(Nat n1, Nat n2, const char* file, uint32_t line)
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Nat subtraction underflow"); }
            int64_t result = 0;
            if(!__builtin_sub_overflow(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(Nat n1, Nat n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(!__builtin_mul_overflow(n1.value, n2.value, &result) || !(Nat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat multiplication bounds"); }
        }
        inline static void checkDivisionByZero(Nat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Nat division by zero"); }
        }

        // Overloaded operators on Nat
        constexpr Nat operator+() const
        {
            return Nat(this->value);
        }
        // Negation is not defined for Nat

        friend constexpr Nat operator+(Nat lhs, Nat rhs)
        {
            return Nat(lhs.value + rhs.value);
        }
        friend constexpr Nat operator-(Nat lhs, Nat rhs)
        {
            return Nat(lhs.value - rhs.value);
        }
        friend constexpr Nat operator/(Nat lhs, Nat rhs)
        {
           return Nat(lhs.value / rhs.value);
        }
        friend constexpr Nat operator*(Nat lhs, Nat rhs)
        {
            return Nat(lhs.value * rhs.value);
        }

        friend constexpr bool operator<(const Nat &lhs, const Nat &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const Nat &lhs, const Nat &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const Nat &lhs, const Nat &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const Nat &lhs, const Nat &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const Nat &lhs, const Nat &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const Nat &lhs, const Nat &rhs) { return !(lhs.value < rhs.value); }
    };

    class Int
    {
    public:
        static constexpr int64_t MIN_INT = -ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 
        static constexpr int64_t MAX_INT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 

        inline constexpr static bool isValidInt(int64_t v)
        {
            return (Int::MIN_INT <= v) & (v <= Int::MAX_INT);
        }

    private:
        int64_t value;

    public:
        constexpr Int() : value(0) {}
        constexpr Int(int64_t v) : value(v) {}
        constexpr Int(const Int& other) = default;

        inline constexpr int64_t getValue() const { return this->value; }

        // Check operators on Int
        inline static void checkOverflowAddition(Int n1, Int n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(!__builtin_add_overflow(n1.value, n2.value, &result) || !(Int::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int addition bounds"); }
        }
        inline static void checkOverflowSubtraction(Int n1, Int n2, const char* file, uint32_t line)
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Int subtraction underflow"); }
            int64_t result = 0;
            if(!__builtin_sub_overflow(n1.value, n2.value, &result) || !(Int::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(Int n1, Int n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(!__builtin_mul_overflow(n1.value, n2.value, &result) || !(Int::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int multiplication bounds"); }
        }
        inline static void checkDivisionByZero(Int n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Int
        constexpr Int operator+() const
        {
            return Int(this->value);
        }
        constexpr Int operator-() const
        {
            return Int(-this->value);
        }

        friend constexpr Int operator+(Int lhs, Int rhs)
        {
            return Int(lhs.value + rhs.value);
        }
        friend constexpr Int operator-(Int lhs, Int rhs)
        {
            return Int(lhs.value - rhs.value);
        }
        friend constexpr Int operator/(Int lhs, Int rhs)
        {
            return Int(lhs.value / rhs.value);
        }
        friend constexpr Int operator*(Int lhs, Int rhs)
        {
            return Int(lhs.value * rhs.value);
        }

        friend constexpr bool operator<(const Int &lhs, const Int &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const Int &lhs, const Int &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const Int &lhs, const Int &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const Int &lhs, const Int &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const Int &lhs, const Int &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const Int &lhs, const Int &rhs) { return !(lhs.value < rhs.value); }
    };

    class ChkNat
    {
    public:
        static constexpr __int128_t MAX_NAT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        inline constexpr static bool isValidNat(__int128_t v)
        {
            return (0 <= v) & (v <= ChkNat::MAX_NAT);
        }

    private:
        __int128_t value;

        static constexpr __int128_t BOTTOM_VALUE = (__int128_t(1) << 126);

        inline constexpr static bool s_isBottom(__int128_t v)
        {
            return (v & BOTTOM_VALUE) != 0;
        }

    public:
        constexpr ChkNat() : value(0) {}
        constexpr ChkNat(__int128_t v) : value(v) {}
        constexpr ChkNat(const ChkNat& other) = default;

        inline constexpr __int128_t getValue() const { return this->value; }

        constexpr static ChkNat bliteral()
        {
            return ChkNat(ChkNat::BOTTOM_VALUE);
        }

        constexpr bool isBottom() const
        {
            return ChkNat::s_isBottom(this->value);
        }

        inline static void checkOverflowSubtraction(ChkNat n1, ChkNat n2, const char* file, uint32_t line)
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Nat subtraction underflow"); }
        }
        inline static void checkDivisionByZero(ChkNat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Nat
        constexpr ChkNat operator+() const
        {
            return ChkNat(this->value);
        }
        // Negation is not defined for Nat

        friend constexpr ChkNat operator+(ChkNat lhs, ChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return ChkNat(ChkNat::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_add_overflow(lhs.value, rhs.value, &result) && (ChkNat::isValidNat(result))) [[likely]] {
                return ChkNat(result);
            }
            else {
                return ChkNat(ChkNat::BOTTOM_VALUE);
            }
        }
        friend constexpr ChkNat operator-(ChkNat lhs, ChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return ChkNat(ChkNat::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_sub_overflow(lhs.value, rhs.value, &result) && (ChkNat::isValidNat(result))) [[likely]] {
                return ChkNat(result);
            }
            else {
                return ChkNat(ChkNat::BOTTOM_VALUE);
            }
        }
        friend constexpr ChkNat operator/(ChkNat lhs, ChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return ChkNat(ChkNat::BOTTOM_VALUE);
            }

            return ChkNat(lhs.value / rhs.value);
        }
        friend constexpr ChkNat operator*(ChkNat lhs, ChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return ChkNat(ChkNat::BOTTOM_VALUE);
            }

           __int128_t result = 0;
            if(!__builtin_mul_overflow(lhs.value, rhs.value, &result) && (ChkNat::isValidNat(result))) [[likely]] {
                return ChkNat(result);
            }
            else {
                return ChkNat(ChkNat::BOTTOM_VALUE);
            }
        }

        friend constexpr bool operator<(const ChkNat &lhs, const ChkNat &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const ChkNat &lhs, const ChkNat &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const ChkNat &lhs, const ChkNat &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const ChkNat &lhs, const ChkNat &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const ChkNat &lhs, const ChkNat &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const ChkNat &lhs, const ChkNat &rhs) { return !(lhs.value < rhs.value); }
    };

    class ChkInt
    {
    public:
        static constexpr __int128_t MIN_INT = -ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 
        static constexpr __int128_t MAX_INT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        inline constexpr static bool isValidInt(__int128_t v)
        {
            return (ChkInt::MIN_INT <= v) & (v <= ChkInt::MAX_INT);
        }

    private:
        __int128_t value;
        
        static constexpr __int128_t BOTTOM_VALUE = (__int128_t(1) << 126);

        inline constexpr static bool isBottom(__int128_t v)
        {
            return (v & BOTTOM_VALUE) != 0;
        }

    public:
        constexpr ChkInt() : value(0) {}
        constexpr ChkInt(__int128_t v) : value(v) {}
        constexpr ChkInt(const ChkInt& other) = default;

        inline constexpr __int128_t getValue() const { return this->value; }

        constexpr bool isBottom() const
        {
            return ChkInt::isBottom(this->value);
        }

        constexpr static ChkInt bliteral()
        {
            return ChkInt(ChkInt::BOTTOM_VALUE);
        }
    
        inline static void checkDivisionByZero(ChkInt n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Int
        constexpr ChkInt operator+() const
        {
            return ChkInt(this->value);
        }
        constexpr ChkInt operator-() const
        {
            return ChkInt(-this->value);
        }

        friend constexpr ChkInt operator+(ChkInt lhs, ChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return ChkInt(ChkInt::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_add_overflow(lhs.value, rhs.value, &result) && (ChkInt::isValidInt(result))) [[likely]] {
                return ChkInt(result);
            }
            else {
                return ChkInt(ChkInt::BOTTOM_VALUE);
            }
        }
        friend constexpr ChkInt operator-(ChkInt lhs, ChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return ChkInt(ChkInt::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_sub_overflow(lhs.value, rhs.value, &result) && (ChkInt::isValidInt(result))) [[likely]] {
                return ChkInt(result);
            }
            else {
                return ChkInt(ChkInt::BOTTOM_VALUE);
            }
        }
        friend constexpr ChkInt operator/(ChkInt lhs, ChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return ChkInt(ChkInt::BOTTOM_VALUE);
            }

            return ChkInt(lhs.value / rhs.value);
        }
        friend constexpr ChkInt operator*(ChkInt lhs, ChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return ChkInt(ChkInt::BOTTOM_VALUE);
            }

           __int128_t result = 0;
            if(!__builtin_mul_overflow(lhs.value, rhs.value, &result) && (ChkInt::isValidInt(result))) [[likely]] {
                return ChkInt(result);
            }
            else {
                return ChkInt(ChkInt::BOTTOM_VALUE);
            }
        }

        friend constexpr bool operator<(const ChkInt &lhs, const ChkInt &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const ChkInt &lhs, const ChkInt &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const ChkInt &lhs, const ChkInt &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const ChkInt &lhs, const ChkInt &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const ChkInt &lhs, const ChkInt &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const ChkInt &lhs, const ChkInt &rhs) { return !(lhs.value < rhs.value); }
    };

    static_assert(sizeof(Nat) == sizeof(int64_t), "Nat size incorrect");
    static_assert(sizeof(Int) == sizeof(int64_t), "Int size incorrect");
    static_assert(sizeof(ChkNat) == sizeof(__int128_t), "BigNat size incorrect");
    static_assert(sizeof(ChkInt) == sizeof(__int128_t), "BigInt size incorrect");
}
