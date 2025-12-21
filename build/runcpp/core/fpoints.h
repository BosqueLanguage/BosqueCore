#pragma once

#include "../common.h"

#include "bsqtype.h"

namespace ᐸRuntimeᐳ 
{
    class XFloat
    {
    public:
        inline constexpr static bool isValidFloat(double v)
        {
            return std::isfinite(v);
        }

    private:
        double value;

    public:
        constexpr XFloat() : value(0) {}
        constexpr XFloat(double v) : value(v) {}
        constexpr XFloat(const XFloat& other) = default;

        inline constexpr double getValue() const { return this->value; }

        // Check operators on Float
        inline static void checkOverflowAddition(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value + n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float addition bounds"); }
        }
        inline static void checkOverflowSubtraction(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value - n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float subtraction bounds"); }
        }
        inline static void checkOverflowMultiplication(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value * n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float multiplication bounds"); }
        }
        inline static void checkDivisionByZero(XFloat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0.0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Nat division by zero"); }
        }

        // Overloaded operators on Float
        constexpr XFloat operator+() const
        {
            return XFloat(this->value);
        }
        // Negation is not defined for Nat

        friend constexpr XFloat operator+(XFloat lhs, XFloat rhs)
        {
            return XFloat(lhs.value + rhs.value);
        }
        friend constexpr XFloat operator-(XFloat lhs, XFloat rhs)
        {
            return XFloat(lhs.value - rhs.value);
        }
        friend constexpr XFloat operator/(XFloat lhs, XFloat rhs)
        {
           return XFloat(lhs.value / rhs.value);
        }
        friend constexpr XFloat operator*(XFloat lhs, XFloat rhs)
        {
            return XFloat(lhs.value * rhs.value);
        }

        friend constexpr bool operator<(const XFloat &lhs, const XFloat &rhs) { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const XFloat &lhs, const XFloat &rhs) { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const XFloat &lhs, const XFloat &rhs) { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const XFloat &lhs, const XFloat &rhs) { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const XFloat &lhs, const XFloat &rhs) { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const XFloat &lhs, const XFloat &rhs) { return !(lhs.value < rhs.value); }
    };

    constexpr TypeInfo g_typeinfo_Float = {
        WELL_KNOWN_TYPE_ID_FLOAT,
        sizeof(XFloat),
        byteSizeToSlotCount(sizeof(XFloat)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        "Float",
        nullptr
    };

    static_assert(sizeof(XFloat) == sizeof(double), "Float size incorrect");
}
