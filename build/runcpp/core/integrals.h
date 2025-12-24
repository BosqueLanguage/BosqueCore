#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ 
{
    class XNat
    {
    public:
        static constexpr int64_t MAX_NAT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE;

        inline constexpr static bool isValidNat(int64_t v)
        {
            return (0 <= v) & (v <= XNat::MAX_NAT);
        }

    private:
        int64_t value;

    public:
        constexpr XNat() : value(0) {}
        constexpr XNat(int64_t v) : value(v) {}
        constexpr XNat(const XNat& other) = default;

        inline constexpr int64_t getValue() const { return this->value; }

        // Check operators on Nat
        inline static void checkOverflowAddition(XNat n1, XNat n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_add_overflow(n1.value, n2.value, &result) || !(XNat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat addition bounds"); }
        }
        inline static void checkOverflowSubtraction(XNat n1, XNat n2, const char* file, uint32_t line)
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Nat subtraction underflow"); }
            
            int64_t result = 0;
            if(__builtin_sub_overflow(n1.value, n2.value, &result) || !(XNat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(XNat n1, XNat n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_mul_overflow(n1.value, n2.value, &result) || !(XNat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat multiplication bounds"); }
        }
        inline static void checkDivisionByZero(XNat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Nat division by zero"); }
        }

        // Overloaded operators on Nat
        constexpr XNat operator+() const
        {
            return XNat(this->value);
        }
        // Negation is not defined for Nat

        friend constexpr XNat operator+(XNat lhs, XNat rhs)
        {
            return XNat(lhs.value + rhs.value);
        }
        friend constexpr XNat operator-(XNat lhs, XNat rhs)
        {
            return XNat(lhs.value - rhs.value);
        }
        friend constexpr XNat operator/(XNat lhs, XNat rhs)
        {
           return XNat(lhs.value / rhs.value);
        }
        friend constexpr XNat operator*(XNat lhs, XNat rhs)
        {
            return XNat(lhs.value * rhs.value);
        }

        friend constexpr bool operator<(const XNat& lhs, const XNat& rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XNat& lhs, const XNat& rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XNat& lhs, const XNat& rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XNat& lhs, const XNat& rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XNat& lhs, const XNat& rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XNat& lhs, const XNat& rhs) { return !(lhs.value < rhs.value); }
    };

    class XInt
    {
    public:
        static constexpr int64_t MIN_INT = -ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 
        static constexpr int64_t MAX_INT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 

        inline constexpr static bool isValidInt(int64_t v)
        {
            return (XInt::MIN_INT <= v) & (v <= XInt::MAX_INT);
        }

    private:
        int64_t value;

    public:
        constexpr XInt() : value(0) {}
        constexpr XInt(int64_t v) : value(v) {}
        constexpr XInt(const XInt& other) = default;

        inline constexpr int64_t getValue() const { return this->value; }

        // Check operators on Int
        inline static void checkOverflowAddition(XInt n1, XInt n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_add_overflow(n1.value, n2.value, &result) || !(XInt::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int addition bounds"); }
        }
        inline static void checkOverflowSubtraction(XInt n1, XInt n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_sub_overflow(n1.value, n2.value, &result) || !(XInt::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(XInt n1, XInt n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_mul_overflow(n1.value, n2.value, &result) || !(XInt::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int multiplication bounds"); }
        }
        inline static void checkDivisionByZero(XInt n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Int
        constexpr XInt operator+() const
        {
            return XInt(this->value);
        }
        constexpr XInt operator-() const
        {
            return XInt(-this->value);
        }

        friend constexpr XInt operator+(XInt lhs, XInt rhs)
        {
            return XInt(lhs.value + rhs.value);
        }
        friend constexpr XInt operator-(XInt lhs, XInt rhs)
        {
            return XInt(lhs.value - rhs.value);
        }
        friend constexpr XInt operator/(XInt lhs, XInt rhs)
        {
            return XInt(lhs.value / rhs.value);
        }
        friend constexpr XInt operator*(XInt lhs, XInt rhs)
        {
            return XInt(lhs.value * rhs.value);
        }

        friend constexpr bool operator<(const XInt& lhs, const XInt& rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XInt& lhs, const XInt& rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XInt& lhs, const XInt& rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XInt& lhs, const XInt& rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XInt& lhs, const XInt& rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XInt& lhs, const XInt& rhs) { return !(lhs.value < rhs.value); }
    };

    class XChkNat
    {
    public:
        static constexpr __int128_t MAX_NAT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        inline constexpr static bool isValidNat(__int128_t v)
        {
            return (0 <= v) & (v <= XChkNat::MAX_NAT);
        }

    private:
        __int128_t value;

        static constexpr __int128_t BOTTOM_VALUE = (__int128_t(1) << 126);

        inline constexpr static bool s_isBottom(__int128_t v)
        {
            return (v & BOTTOM_VALUE) != 0;
        }

    public:
        constexpr XChkNat() : value(0) {}
        constexpr XChkNat(__int128_t v) : value(v) {}
        constexpr XChkNat(const XChkNat& other) = default;

        inline constexpr __int128_t getValue() const { return this->value; }

        constexpr static XChkNat bliteral()
        {
            return XChkNat(XChkNat::BOTTOM_VALUE);
        }

        constexpr bool isBottom() const
        {
            return XChkNat::s_isBottom(this->value);
        }

        inline static void checkOverflowSubtraction(XChkNat n1, XChkNat n2, const char* file, uint32_t line)
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Nat subtraction underflow"); }
        }
        inline static void checkDivisionByZero(XChkNat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Nat
        constexpr XChkNat operator+() const
        {
            return XChkNat(this->value);
        }
        // Negation is not defined for Nat

        friend constexpr XChkNat operator+(XChkNat lhs, XChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkNat(XChkNat::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_add_overflow(lhs.value, rhs.value, &result) && XChkNat::isValidNat(result)) [[likely]] {
                return XChkNat(result);
            }
            else {
                return XChkNat(XChkNat::BOTTOM_VALUE);
            }
        }
        friend constexpr XChkNat operator-(XChkNat lhs, XChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkNat(XChkNat::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_sub_overflow(lhs.value, rhs.value, &result) && XChkNat::isValidNat(result)) [[likely]] {
                return XChkNat(result);
            }
            else {
                return XChkNat(XChkNat::BOTTOM_VALUE);
            }
        }
        friend constexpr XChkNat operator/(XChkNat lhs, XChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkNat(XChkNat::BOTTOM_VALUE);
            }

            return XChkNat(lhs.value / rhs.value);
        }
        friend constexpr XChkNat operator*(XChkNat lhs, XChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkNat(XChkNat::BOTTOM_VALUE);
            }

           __int128_t result = 0;
            if(!__builtin_mul_overflow(lhs.value, rhs.value, &result) && XChkNat::isValidNat(result)) [[likely]] {
                return XChkNat(result);
            }
            else {
                return XChkNat(XChkNat::BOTTOM_VALUE);
            }
        }

        friend constexpr bool operator<(const XChkNat& lhs, const XChkNat& rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XChkNat& lhs, const XChkNat& rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XChkNat& lhs, const XChkNat& rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XChkNat& lhs, const XChkNat& rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XChkNat& lhs, const XChkNat& rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XChkNat& lhs, const XChkNat& rhs) { return !(lhs.value < rhs.value); }
    };

    class XChkInt
    {
    public:
        static constexpr __int128_t MIN_INT = -ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 
        static constexpr __int128_t MAX_INT = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        inline constexpr static bool isValidInt(__int128_t v)
        {
            return (XChkInt::MIN_INT <= v) & (v <= XChkInt::MAX_INT);
        }

    private:
        __int128_t value;
        
        static constexpr __int128_t BOTTOM_VALUE = (__int128_t(1) << 126);

        inline constexpr static bool isBottom(__int128_t v)
        {
            return (v & BOTTOM_VALUE) != 0;
        }

    public:
        constexpr XChkInt() : value(0) {}
        constexpr XChkInt(__int128_t v) : value(v) {}
        constexpr XChkInt(const XChkInt& other) = default;

        inline constexpr __int128_t getValue() const { return this->value; }

        constexpr bool isBottom() const
        {
            return XChkInt::isBottom(this->value);
        }

        constexpr static XChkInt bliteral()
        {
            return XChkInt(XChkInt::BOTTOM_VALUE);
        }
    
        inline static void checkDivisionByZero(XChkInt n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Int
        constexpr XChkInt operator+() const
        {
            return XChkInt(this->value);
        }
        constexpr XChkInt operator-() const
        {
            return XChkInt(-this->value);
        }

        friend constexpr XChkInt operator+(XChkInt lhs, XChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkInt(XChkInt::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_add_overflow(lhs.value, rhs.value, &result) && XChkInt::isValidInt(result)) [[likely]] {
                return XChkInt(result);
            }
            else {
                return XChkInt(XChkInt::BOTTOM_VALUE);
            }
        }
        friend constexpr XChkInt operator-(XChkInt lhs, XChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkInt(XChkInt::BOTTOM_VALUE);
            }

            __int128_t result = 0;
            if(!__builtin_sub_overflow(lhs.value, rhs.value, &result) && XChkInt::isValidInt(result)) [[likely]] {
                return XChkInt(result);
            }
            else {
                return XChkInt(XChkInt::BOTTOM_VALUE);
            }
        }
        friend constexpr XChkInt operator/(XChkInt lhs, XChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkInt(XChkInt::BOTTOM_VALUE);
            }

            return XChkInt(lhs.value / rhs.value);
        }
        friend constexpr XChkInt operator*(XChkInt lhs, XChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkInt(XChkInt::BOTTOM_VALUE);
            }

           __int128_t result = 0;
            if(!__builtin_mul_overflow(lhs.value, rhs.value, &result) && XChkInt::isValidInt(result)) [[likely]] {
                return XChkInt(result);
            }
            else {
                return XChkInt(XChkInt::BOTTOM_VALUE);
            }
        }

        friend constexpr bool operator<(const XChkInt& lhs, const XChkInt& rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XChkInt& lhs, const XChkInt& rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XChkInt& lhs, const XChkInt& rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XChkInt& lhs, const XChkInt& rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XChkInt& lhs, const XChkInt& rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XChkInt& lhs, const XChkInt& rhs) { return !(lhs.value < rhs.value); }
    };

    constexpr TypeInfo g_typeinfo_Nat = {
        WELL_KNOWN_TYPE_ID_NAT,
        sizeof(XNat),
        byteSizeToSlotCount(sizeof(XNat)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "Nat",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_Int = {
        WELL_KNOWN_TYPE_ID_INT,
        sizeof(XInt),
        byteSizeToSlotCount(sizeof(XInt)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "Int",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_ChkNat = {
        WELL_KNOWN_TYPE_ID_CHKNAT,
        sizeof(XChkNat),
        byteSizeToSlotCount(sizeof(XChkNat)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "ChkNat",
        nullptr
    };

    constexpr TypeInfo g_typeinfo_ChkInt = {
        WELL_KNOWN_TYPE_ID_CHKINT,
        sizeof(XChkInt),
        byteSizeToSlotCount(sizeof(XChkInt)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "ChkInt",
        nullptr
    };

    static_assert(sizeof(XNat) == sizeof(int64_t), "Nat size incorrect");
    static_assert(sizeof(XInt) == sizeof(int64_t), "Int size incorrect");
    static_assert(sizeof(XChkNat) == sizeof(__int128_t), "BigNat size incorrect");
    static_assert(sizeof(XChkInt) == sizeof(__int128_t), "BigInt size incorrect");
}
