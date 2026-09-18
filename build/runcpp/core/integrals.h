#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "bool.h"

namespace ᐸRuntimeᐳ 
{
    template<typename T, typename I>
    inline T integerPower(T x, T y)
    {
        if(y.value == 0) {
            return T{1};
        }
        else if(y.value == 1) {
            return x;
        }
        else {
            if(x.value == 0) {
                return T{0};
            }
            else if(x.value == 1) {
                return T{1};
            }
            else {
                if (x.value == 2 && y.value < 60) {
                    return T{((I)1) << (uint32_t)y.value};
                }
                else {
                    T result = T{1};

                    I pval = y.value;
                    while(pval > 0) {
                        if(pval & 1) {
                            T::checkOverflowMultiplication(result, x, "Integral power", 0);
                            result = result * x;
                        }
                        T::checkOverflowMultiplication(x, x, "Integral power", 0);
                        x = x * x;
                        pval >>= 1;
                    }
                    return result;
                }
            }
        }
    }

    class XNat
    {
    public:
        constexpr static int64_t MIN_VALUE = 0;
        constexpr static int64_t MAX_VALUE = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE;

        using value_type = int64_t;

        int64_t value;

        static bool isValidNat(int64_t v)
        {
            return (XNat::MIN_VALUE <= v) & (v <= XNat::MAX_VALUE);
        }

        //Just used internally for range fill and such
        XNat& operator++() {
            ++value;
            return *this;
        }

        // Check operators on Nat
        static void checkOverflowAddition(XNat n1, XNat n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_add_overflow(n1.value, n2.value, &result) || !(XNat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat addition bounds"); }
        }
        static void checkOverflowSubtraction(XNat n1, XNat n2, const char* file, uint32_t line)
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Nat subtraction underflow"); }
            
            int64_t result = 0;
            if(__builtin_sub_overflow(n1.value, n2.value, &result) || !(XNat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat subtraction bounds"); }
        }
        static void checkOverflowMultiplication(XNat n1, XNat n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_mul_overflow(n1.value, n2.value, &result) || !(XNat::isValidNat(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Nat multiplication bounds"); }
        }
        static void checkDivisionByZero(XNat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Nat division by zero"); }
        }

        // Overloaded operators on Nat
        XNat operator+() const
        {
            return *this;
        }
        // Negation is not defined for Nat

        friend XNat operator+(XNat lhs, XNat rhs)
        {
            return XNat{lhs.value + rhs.value};
        }
        friend XNat operator-(XNat lhs, XNat rhs)
        {
            return XNat{lhs.value - rhs.value};
        }
        friend XNat operator/(XNat lhs, XNat rhs)
        {
           return XNat{lhs.value / rhs.value};
        }
        friend XNat operator*(XNat lhs, XNat rhs)
        {
            return XNat{lhs.value * rhs.value};
        }

        friend XBool operator==(const XNat& lhs, const XNat& rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XNat& lhs, const XNat& rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XNat& lhs, const XNat& rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XNat& lhs, const XNat& rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XNat& lhs, const XNat& rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XNat& lhs, const XNat& rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XInt
    {
    public:
        constexpr static int64_t MIN_VALUE = -ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 
        constexpr static int64_t MAX_VALUE = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_BASE; 

        using value_type = int64_t;

        int64_t value;

        static bool isValidInt(int64_t v)
        {
            return (XInt::MIN_VALUE <= v) & (v <= XInt::MAX_VALUE);
        }
    
        //Just used internally for range fill and such
        XInt& operator++() {
            ++value;
            return *this;
        }

        // Check operators on Int
        static void checkOverflowAddition(XInt n1, XInt n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_add_overflow(n1.value, n2.value, &result) || !(XInt::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int addition bounds"); }
        }
        static void checkOverflowSubtraction(XInt n1, XInt n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_sub_overflow(n1.value, n2.value, &result) || !(XInt::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int subtraction bounds"); }
        }
        static void checkOverflowMultiplication(XInt n1, XInt n2, const char* file, uint32_t line)
        {
            int64_t result = 0;
            if(__builtin_mul_overflow(n1.value, n2.value, &result) || !(XInt::isValidInt(result))) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericBounds, nullptr, "Int multiplication bounds"); }
        }
        static void checkDivisionByZero(XInt n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Int
        XInt operator+() const
        {
            return *this;
        }
        XInt operator-() const
        {
            return XInt{-this->value};
        }

        friend XInt operator+(XInt lhs, XInt rhs)
        {
            return XInt{lhs.value + rhs.value};
        }
        friend XInt operator-(XInt lhs, XInt rhs)
        {
            return XInt{lhs.value - rhs.value};
        }
        friend XInt operator/(XInt lhs, XInt rhs)
        {
            return XInt{lhs.value / rhs.value};
        }
        friend XInt operator*(XInt lhs, XInt rhs)
        {
            return XInt{lhs.value * rhs.value};
        }

        friend XBool operator==(const XInt& lhs, const XInt& rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XInt& lhs, const XInt& rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XInt& lhs, const XInt& rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XInt& lhs, const XInt& rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XInt& lhs, const XInt& rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XInt& lhs, const XInt& rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XChkNat
    {
    public:
        constexpr static __int128_t MIN_VALUE = 0;
        constexpr static __int128_t MAX_VALUE = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 

        using value_type = __int128_t;

        __int128_t value;

        static bool isValidNat(__int128_t v)
        {
            return (XChkNat::MIN_VALUE <= v) & (v <= XChkNat::MAX_VALUE);
        }

        constexpr static __int128_t BOTTOM_VALUE = (__int128_t(1) << 126);
        
        static bool s_isBottom(__int128_t v)
        {
            return v == BOTTOM_VALUE;
        }

        consteval static XChkNat bliteral()
        {
            return XChkNat{XChkNat::BOTTOM_VALUE};
        }

        bool isBottom() const
        {
            return XChkNat::s_isBottom(this->value);
        }

        static void checkOverflowAddition(XChkNat n1, XChkNat n2, const char* file, uint32_t line)
        {
            ;
        }
        static void checkOverflowSubtraction(XChkNat n1, XChkNat n2, const char* file, uint32_t line)
        {
            if(n2.value > n1.value) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::NumericUnderflow, nullptr, "Nat subtraction underflow"); }
        }
        static void checkOverflowMultiplication(XChkNat n1, XChkNat n2, const char* file, uint32_t line)
        {
            ;
        }
        static void checkDivisionByZero(XChkNat n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Nat division by zero"); }
        }

        // Overloaded operators on Nat
        XChkNat operator+() const
        {
            return *this;
        }
        // Negation is not defined for Nat

        friend XChkNat operator+(XChkNat lhs, XChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkNat{XChkNat::BOTTOM_VALUE};
            }

            __int128_t result = 0;
            if(!__builtin_add_overflow(lhs.value, rhs.value, &result) && XChkNat::isValidNat(result)) [[likely]] {
                return XChkNat{result};
            }
            else {
                return XChkNat{XChkNat::BOTTOM_VALUE};
            }
        }
        friend XChkNat operator-(XChkNat lhs, XChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkNat{XChkNat::BOTTOM_VALUE};
            }

            __int128_t result = 0;
            if(!__builtin_sub_overflow(lhs.value, rhs.value, &result) && XChkNat::isValidNat(result)) [[likely]] {
                return XChkNat{result};
            }
            else {
                return XChkNat{XChkNat::BOTTOM_VALUE};
            }
        }
        friend XChkNat operator/(XChkNat lhs, XChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkNat{XChkNat::BOTTOM_VALUE};
            }

            return XChkNat{lhs.value / rhs.value};
        }
        friend XChkNat operator*(XChkNat lhs, XChkNat rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkNat{XChkNat::BOTTOM_VALUE};
            }

            __int128_t result = 0;
            if(!__builtin_mul_overflow(lhs.value, rhs.value, &result) && XChkNat::isValidNat(result)) [[likely]] {
                return XChkNat{result};
            }
            else {
                return XChkNat{XChkNat::BOTTOM_VALUE};
            }
        }

        friend XBool operator==(const XChkNat& lhs, const XChkNat& rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XChkNat& lhs, const XChkNat& rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XChkNat& lhs, const XChkNat& rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XChkNat& lhs, const XChkNat& rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XChkNat& lhs, const XChkNat& rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XChkNat& lhs, const XChkNat& rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    class XChkInt
    {
    public:
        constexpr static __int128_t MIN_VALUE = -ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 
        constexpr static __int128_t MAX_VALUE = ᐸRuntimeᐳ::BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED; 
                
        using value_type = __int128_t;

        __int128_t value;

        static bool isValidInt(__int128_t v)
        {
            return (XChkInt::MIN_VALUE <= v) & (v <= XChkInt::MAX_VALUE);
        }

        constexpr static __int128_t BOTTOM_VALUE = (__int128_t(1) << 126);

        static bool s_isBottom(__int128_t v)
        {
            return v == BOTTOM_VALUE;
        }

        consteval static XChkInt bliteral()
        {
            return XChkInt{XChkInt::BOTTOM_VALUE};
        }
    
        bool isBottom() const
        {
            return XChkInt::s_isBottom(this->value);
        }

        static void checkOverflowAddition(XChkInt n1, XChkInt n2, const char* file, uint32_t line)
        {
            ;
        }
        static void checkOverflowSubtraction(XChkInt n1, XChkInt n2, const char* file, uint32_t line)
        {
            ;
        }
        static void checkOverflowMultiplication(XChkInt n1, XChkInt n2, const char* file, uint32_t line)
        {
            ;
        }
        static void checkDivisionByZero(XChkInt n2, const char* file, uint32_t line)
        {
            if(n2.value == 0) [[unlikely]] { ᐸRuntimeᐳ::bsq_handle_error(file, line, ᐸRuntimeᐳ::ErrorKind::DivisionByZero, nullptr, "Int division by zero"); }
        }

        // Overloaded operators on Int
        XChkInt operator+() const
        {
            return *this;
        }
        XChkInt operator-() const
        {
            if(this->isBottom()) {
                return XChkInt{XChkInt::BOTTOM_VALUE};
            }
            else {
                return XChkInt{-this->value};
            }
        }

        friend XChkInt operator+(XChkInt lhs, XChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkInt{XChkInt::BOTTOM_VALUE};
            }

            __int128_t result = 0;
            if(!__builtin_add_overflow(lhs.value, rhs.value, &result) && XChkInt::isValidInt(result)) [[likely]] {
                return XChkInt{result};
            }
            else {
                return XChkInt{XChkInt::BOTTOM_VALUE};
            }
        }
        friend XChkInt operator-(XChkInt lhs, XChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkInt{XChkInt::BOTTOM_VALUE};
            }

            __int128_t result = 0;
            if(!__builtin_sub_overflow(lhs.value, rhs.value, &result) && XChkInt::isValidInt(result)) [[likely]] {
                return XChkInt{result};
            }
            else {
                return XChkInt{XChkInt::BOTTOM_VALUE};
            }
        }
        friend XChkInt operator/(XChkInt lhs, XChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkInt{XChkInt::BOTTOM_VALUE};
            }

            return XChkInt{lhs.value / rhs.value};
        }
        friend XChkInt operator*(XChkInt lhs, XChkInt rhs)
        {
            if(lhs.isBottom() | rhs.isBottom()) {
                return XChkInt{XChkInt::BOTTOM_VALUE};
            }

            __int128_t result = 0;
            if(!__builtin_mul_overflow(lhs.value, rhs.value, &result) && XChkInt::isValidInt(result)) [[likely]] {
                return XChkInt{result};
            }
            else {
                return XChkInt{XChkInt::BOTTOM_VALUE};
            }
        }

        friend XBool operator==(const XChkInt& lhs, const XChkInt& rhs) { return XBool::from(lhs.value == rhs.value); }
        friend XBool operator<(const XChkInt& lhs, const XChkInt& rhs) { return XBool::from(lhs.value < rhs.value); }
        friend XBool operator>(const XChkInt& lhs, const XChkInt& rhs) { return XBool::from(rhs.value < lhs.value); }
        friend XBool operator!=(const XChkInt& lhs, const XChkInt& rhs) { return XBool::from(!(lhs.value == rhs.value)); }
        friend XBool operator<=(const XChkInt& lhs, const XChkInt& rhs) { return XBool::from(!(lhs.value > rhs.value)); }
        friend XBool operator>=(const XChkInt& lhs, const XChkInt& rhs) { return XBool::from(!(lhs.value < rhs.value)); }
    };

    void jsonParseToBSQ_Nat(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_Nat(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_Nat(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_Nat(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_Nat(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_Nat = {
        WELL_KNOWN_TYPE_ID_NAT,
        sizeof(XNat),
        byteSizeToSlotCount(sizeof(XNat)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_Nat, (ParseToBSQFp)&parseToBSQ_Nat, (BSQToJSONFp)&bsqToJSON_Nat, (BSQToBAPIFp)&bsqToBAPI_Nat, (DisplayValueFp)&displayValue_Nat },
        "Nat",
        true
    };

    void jsonParseToBSQ_Int(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_Int(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_Int(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_Int(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_Int(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_Int = {
        WELL_KNOWN_TYPE_ID_INT,
        sizeof(XInt),
        byteSizeToSlotCount(sizeof(XInt)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_Int, (ParseToBSQFp)&parseToBSQ_Int, (BSQToJSONFp)&bsqToJSON_Int, (BSQToBAPIFp)&bsqToBAPI_Int, (DisplayValueFp)&displayValue_Int },
        "Int",
        true
    };

    void jsonParseToBSQ_ChkNat(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_ChkNat(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_ChkNat(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_ChkNat(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_ChkNat(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_ChkNat = {
        WELL_KNOWN_TYPE_ID_CHKNAT,
        sizeof(XChkNat),
        byteSizeToSlotCount(sizeof(XChkNat)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_ChkNat, (ParseToBSQFp)&parseToBSQ_ChkNat, (BSQToJSONFp)&bsqToJSON_ChkNat, (BSQToBAPIFp)&bsqToBAPI_ChkNat, (DisplayValueFp)&displayValue_ChkNat },
        "ChkNat",
        true
    };

    void jsonParseToBSQ_ChkInt(const TypeInfo* tinfo, const json& j, void* resptr);
    void parseToBSQ_ChkInt(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_ChkInt(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_ChkInt(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_ChkInt(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    inline constexpr TypeInfo g_typeinfo_ChkInt = {
        WELL_KNOWN_TYPE_ID_CHKINT,
        sizeof(XChkInt),
        byteSizeToSlotCount(sizeof(XChkInt)),
        LayoutTag::Value,
        BSQ_PTR_MASK_LEAF,
        nullptr,
        0,
        nullptr,
        0,
        nullptr,
        0,
        TypeOpDispatchInfo{ (ValidatingConstructorFp)nullptr, (JSONParseToBSQFp)&jsonParseToBSQ_ChkInt, (ParseToBSQFp)&parseToBSQ_ChkInt, (BSQToJSONFp)&bsqToJSON_ChkInt, (BSQToBAPIFp)&bsqToBAPI_ChkInt, (DisplayValueFp)&displayValue_ChkInt },
        "ChkInt",
        true
    };

    static_assert(sizeof(XNat) == sizeof(int64_t), "Nat size incorrect");
    static_assert(sizeof(XInt) == sizeof(int64_t), "Int size incorrect");
    static_assert(sizeof(XChkNat) == sizeof(__int128_t), "ChkNat size incorrect");
    static_assert(sizeof(XChkInt) == sizeof(__int128_t), "ChkInt size incorrect");
}
