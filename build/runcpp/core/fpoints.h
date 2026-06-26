#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bools.h"

namespace ᐸRuntimeᐳ 
{
    class XFloat
    {
    public:
        double value;

        constexpr static bool isValidFloat(double v)
        {
            return std::isfinite(v);
        }

        template <typename T>
        constexpr static XBool isSafeConvertInto(XFloat f)
        {
            if(!std::isfinite(f.value)) {
                return XBool::from(false);
            }

            return XBool::from((static_cast<double>(T::MIN_VALUE) <= f.value) & (f.value <= static_cast<double>(T::MAX_VALUE)));
        }

        template <typename T>
        constexpr static T doSafeConvertInto(XFloat f)
        {
            return T{static_cast<typename T::value_type>(f.value)};
        }

        // Check operators on Float
        constexpr static void checkOverflowAddition(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value + n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float addition bounds"); }
        }
        constexpr static void checkOverflowSubtraction(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value - n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float subtraction bounds"); }
        }
        constexpr static void checkOverflowMultiplication(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value * n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float multiplication bounds"); }
        }
        constexpr static void checkDivisionByZero(XFloat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0.0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Float division by zero"); }
        }

        // Overloaded operators on Float
        constexpr XFloat operator+() const
        {
            return XFloat{this->value};
        }
        constexpr XFloat operator-() const
        {
            return XFloat{-this->value};
        }

        friend constexpr XFloat operator+(XFloat lhs, XFloat rhs)
        {
            return XFloat{lhs.value + rhs.value};
        }
        friend constexpr XFloat operator-(XFloat lhs, XFloat rhs)
        {
            return XFloat{lhs.value - rhs.value};
        }
        friend constexpr XFloat operator/(XFloat lhs, XFloat rhs)
        {
           return XFloat{lhs.value / rhs.value};
        }
        friend constexpr XFloat operator*(XFloat lhs, XFloat rhs)
        {
            return XFloat{lhs.value * rhs.value};
        }

        friend constexpr XBool operator<(const XFloat &lhs, const XFloat &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend constexpr XBool operator==(const XFloat &lhs, const XFloat &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend constexpr XBool operator>(const XFloat &lhs, const XFloat &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend constexpr XBool operator!=(const XFloat &lhs, const XFloat &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend constexpr XBool operator<=(const XFloat &lhs, const XFloat &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend constexpr XBool operator>=(const XFloat &lhs, const XFloat &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    inline constexpr TypeInfo g_typeinfo_Float = {
        WELL_KNOWN_TYPE_ID_FLOAT,
        sizeof(XFloat),
        byteSizeToSlotCount(sizeof(XFloat)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        "Float",
        true
    };

    static_assert(sizeof(XFloat) == sizeof(double), "Float size incorrect");
}
