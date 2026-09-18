#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bool.h"

namespace ᐸRuntimeᐳ 
{
    class XFloat
    {
    public:
        double value;

        static bool isValidFloat(double v)
        {
            return std::isfinite(v);
        }

        template <typename T>
        static XBool isSafeConvertInto(XFloat f)
        {
            if(!std::isfinite(f.value)) {
                return XBool::from(false);
            }

            return XBool::from((static_cast<double>(T::MIN_VALUE) <= f.value) & (f.value <= static_cast<double>(T::MAX_VALUE)));
        }

        template <typename T>
        static T doSafeConvertInto(XFloat f)
        {
            return T{static_cast<typename T::value_type>(f.value)};
        }

        // Check operators on Float
        static void checkOverflowAddition(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value + n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float addition bounds"); }
        }
        static void checkOverflowSubtraction(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value - n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float subtraction bounds"); }
        }
        static void checkOverflowMultiplication(XFloat n1, XFloat n2, const char* file, uint32_t line)
        {
            if(!(XFloat::isValidFloat(n1.value * n2.value))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Float multiplication bounds"); }
        }
        static void checkDivisionByZero(XFloat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0.0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Float division by zero"); }
        }

        // Overloaded operators on Float
        XFloat operator+() const
        {
            return XFloat{this->value};
        }
        XFloat operator-() const
        {
            return XFloat{-this->value};
        }

        friend XFloat operator+(XFloat lhs, XFloat rhs)
        {
            return XFloat{lhs.value + rhs.value};
        }
        friend XFloat operator-(XFloat lhs, XFloat rhs)
        {
            return XFloat{lhs.value - rhs.value};
        }
        friend XFloat operator/(XFloat lhs, XFloat rhs)
        {
           return XFloat{lhs.value / rhs.value};
        }
        friend XFloat operator*(XFloat lhs, XFloat rhs)
        {
            return XFloat{lhs.value * rhs.value};
        }

        friend XBool operator<(const XFloat &lhs, const XFloat &rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator==(const XFloat &lhs, const XFloat &rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator>(const XFloat &lhs, const XFloat &rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XFloat &lhs, const XFloat &rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XFloat &lhs, const XFloat &rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XFloat &lhs, const XFloat &rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    void jsonParseToBSQ_Float(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_Float(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_Float(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_Float(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_Float(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

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
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_Float, (ParseToBSQFp)&parseToBSQ_Float, (BSQToJSONFp)&bsqToJSON_Float, (BSQToBAPIFp)&bsqToBAPI_Float, (DisplayValueFp)&displayValue_Float },
        "Float",
        true
    };

    static_assert(sizeof(XFloat) == sizeof(double), "Float size incorrect");
}
