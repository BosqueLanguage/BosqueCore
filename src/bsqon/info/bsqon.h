#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"
#include "../regex/bsqpath.h"
#include "type_info.h"

#include <gmp.h>

namespace BSQON
{
    std::optional<char32_t> decodeHexEscape(std::string escc);
    
    UnicodeString resolveEscapeUnicodeFromCode(char32_t c);
    char32_t resolveEscapeUnicodeFromName(const UnicodeString& name);
    std::string resolveEscapeASCIIFromCode(char c);
    char resolveEscapeASCIIFromName(const std::string& name);

    class SourcePos
    {
    public:
        uint32_t first_line;
        uint32_t first_column;
        uint32_t last_line;
        uint32_t last_column;
    };

    class Value
    {
    public:
        const Type* vtype;
        const SourcePos spos;

        Value(const Type* vtype, SourcePos spos) : vtype(vtype), spos(spos) { ; }
        virtual ~Value() = default;

        virtual std::string toString() const = 0;

        virtual bool isErrorValue() const
        {
            return false;
        }

        virtual bool isValidForTypedecl() const
        {
            return false;
        }

        static int keyCompare(const Value* v1, const Value* v2);

        template <typename T>
        static int keyCompareImplScalars(T v1, T v2)
        {
            if(v1 == v2) {
                return 0;
            }
            else if(v1 < v2) {
                return -1;
            }
            else {
                return 1;
            }
        }

        template <typename T>
        static int keyCompareImplStringish(const T& v1, const T& v2)
        {
            if(v1.size() < v2.size()) {
                return -1;
            }
            else if(v1.size() > v2.size()) {
                return 1;
            }
            else {
                auto mmi = std::mismatch(v1.cbegin(), v1.cend(), v2.cbegin(), v2.cend());
                if(mmi.first == v1.cend() && mmi.second == v2.cend()) {
                    return 0;
                }
                else {
                    return *mmi.first < *mmi.second ? -1 : 1;
                }
            }
        }

        static int keyCompareImplArray(uint16_t* v1, uint16_t* v2, size_t length)
        {
            auto mmi = std::mismatch(v1, v1 + length, v2, v2 + length);
            if(mmi.first == v1 + length && mmi.second == v2 + length) {
                return 0;
            }
            else {
                return *mmi.first < *mmi.second ? -1 : 1;
            }
        }
    };

    class ErrorValue : public Value
    {
    public:
        ErrorValue(const Type* vtype, SourcePos spos) : Value(vtype, spos) { ; }
        virtual ~ErrorValue() = default;

        virtual std::string toString() const override
        {
            return "error";
        }

        virtual bool isErrorValue() const override
        {
            return true;
        }
    };

    class PrimtitiveValue : public Value
    {
    public:
        PrimtitiveValue(const Type* vtype, SourcePos spos) : Value(vtype, spos) { ; }
        virtual ~PrimtitiveValue() = default;

        const PrimitiveType* getPrimitiveType() const
        {
            return (const PrimitiveType*)this->vtype;
        }
    };

    class NoneValue : public PrimtitiveValue 
    {
    public:
        NoneValue(const Type* vtype, SourcePos spos) : PrimtitiveValue(vtype, spos) { ; }
        virtual ~NoneValue() = default;

        virtual std::string toString() const override
        {
            return "none";
        }
    };

    class NothingValue : public PrimtitiveValue 
    {
    public:
        NothingValue(const Type* vtype, SourcePos spos) : PrimtitiveValue(vtype, spos) { ; }
        virtual ~NothingValue() = default;

        virtual std::string toString() const override
        {
            return "nothing";
        }
    };

    class BoolValue : public PrimtitiveValue 
    {
    public:
        const bool tv;
    
        BoolValue(const Type* vtype, SourcePos spos, bool tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~BoolValue() = default;

        virtual std::string toString() const override
        {
            return this->tv ? "true" : "false";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const BoolValue* v1, const BoolValue* v2)
        {
            if(v1->tv == v2->tv) {
                return 0;
            }
            else if(!v1->tv) {
                return -1;
            }
            else {
                return 1;
            }
        }
    };

    class NatNumberValue : public PrimtitiveValue 
    {
    public:
        const uint64_t cnv;
    
        NatNumberValue(const Type* vtype, SourcePos spos, uint64_t cnv) : PrimtitiveValue(vtype, spos), cnv(cnv) { ; }
        virtual ~NatNumberValue() = default;

        virtual std::string toString() const override
        {
            return std::to_string(this->cnv) + "n";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const NatNumberValue* v1, const NatNumberValue* v2)
        {
            return Value::keyCompareImplScalars(v1->cnv, v2->cnv);
        }
    };

    class IntNumberValue : public PrimtitiveValue 
    {
    public:
        const int64_t cnv;
        
        IntNumberValue(const Type* vtype, SourcePos spos, int64_t cnv) : PrimtitiveValue(vtype, spos), cnv(cnv) { ; }
        virtual ~IntNumberValue() = default;

        virtual std::string toString() const override
        {
            return std::to_string(this->cnv) + "i";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const IntNumberValue* v1, const IntNumberValue* v2)
        {
            return Value::keyCompareImplScalars(v1->cnv, v2->cnv);
        }
    };

    class BigNatNumberValue : public PrimtitiveValue 
    {
    public:
        mpz_t cnv;
    
        BigNatNumberValue(const Type* vtype, SourcePos spos, mpz_t cnv) : PrimtitiveValue(vtype, spos) 
        { 
            mpz_init_set(this->cnv, cnv); 
        }

        virtual ~BigNatNumberValue()
        {
            mpz_clear(this->cnv);
        }

        virtual std::string toString() const override
        {
            char* cstr = mpz_get_str(NULL, 10, this->cnv);
            std::string str(cstr);

            void (*freefunc)(void *, size_t);
            mp_get_memory_functions (NULL, NULL, &freefunc);
            freefunc(cstr, strlen(cstr) + 1);

            return str + "N";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const BigNatNumberValue* v1, const BigNatNumberValue* v2)
        {
            return Value::keyCompareImplScalars(v1->cnv, v2->cnv);
        }
    };

    class BigIntNumberValue : public PrimtitiveValue 
    {
    public:
        mpz_t cnv;
    
        BigIntNumberValue(const Type* vtype, SourcePos spos, mpz_t cnv) : PrimtitiveValue(vtype, spos) 
        { 
            mpz_init_set(this->cnv, cnv);
        }

        virtual ~BigIntNumberValue()
        {
            mpz_clear(this->cnv);
        }

        virtual std::string toString() const override
        {
            char* cstr = mpz_get_str(NULL, 10, this->cnv);
            std::string str(cstr);

            void (*freefunc)(void *, size_t);
            mp_get_memory_functions (NULL, NULL, &freefunc);
            freefunc(cstr, strlen(cstr) + 1);

            return str + "I";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const BigIntNumberValue* v1, const BigIntNumberValue* v2)
        {
            return Value::keyCompareImplScalars(v1->cnv, v2->cnv);
        }
    };

    class FloatNumberValue : public PrimtitiveValue 
    {
    public:
        const double cnv;
        
        FloatNumberValue(const Type* vtype, SourcePos spos, double cnv) : PrimtitiveValue(vtype, spos), cnv(cnv) { ; }
        virtual ~FloatNumberValue() = default;

        virtual std::string toString() const override
        {
            return std::to_string(this->cnv) + "f";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }
    };

    class DecimalNumberValue : public PrimtitiveValue 
    {
    public:
        //
        //TODO: we need to add a decimal library/implementation
        //
        const std::string cnv;
    
        DecimalNumberValue(const Type* vtype, SourcePos spos, std::string cnv) : PrimtitiveValue(vtype, spos), cnv(cnv) { ; }
        virtual ~DecimalNumberValue() = default;

        virtual std::string toString() const override
        {
            //TODO: decimal needs a bit of work
            return this->cnv + "d";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }
    };

    class RationalNumberValue : public PrimtitiveValue 
    {
    public:
        mpq_t cnv;

        const std::string numerator;
        const uint64_t denominator;
    
        RationalNumberValue(const Type* vtype, SourcePos spos, mpq_t cnv, std::string numerator, uint64_t denominator) : PrimtitiveValue(vtype, spos), numerator(numerator), denominator(denominator) 
        { 
            mpq_init(this->cnv);
            mpq_set(this->cnv, cnv);
        }

        virtual ~RationalNumberValue()
        {
            mpq_clear(this->cnv);
        }

        virtual std::string toString() const override
        {
            char* cstr = mpq_get_str(NULL, 10, this->cnv);
            std::string str(cstr);

            void (*freefunc)(void *, size_t);
            mp_get_memory_functions (NULL, NULL, &freefunc);
            freefunc(cstr, strlen(cstr) + 1);

            return str + "R";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }
    };

    class StringValue : public PrimtitiveValue 
    {
    public:
        const UnicodeString sv;
    
        virtual ~StringValue() = default;

        static StringValue* createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length);

        virtual std::string toString() const override
        {
            auto ustr = escapeString(this->sv);
            return "\"" + std::string(ustr.begin(), ustr.end()) + "\"";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const StringValue* v1, const StringValue* v2)
        {
            return Value::keyCompareImplStringish(v1->sv, v2->sv);
        }

    private:
        StringValue(const Type* vtype, SourcePos spos, UnicodeString&& sv) : PrimtitiveValue(vtype, spos), sv(std::move(sv)) { ; }
    };

    class ASCIIStringValue : public PrimtitiveValue
    {
    public:
        const std::string sv;
    
        virtual ~ASCIIStringValue() = default;

        static ASCIIStringValue* createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length);

        virtual std::string toString() const override
        {
            auto ustr = escapeASCIIString(this->sv);
            return "'" + std::string(ustr.begin(), ustr.end()) + "'";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const ASCIIStringValue* v1, const ASCIIStringValue* v2)
        {
            return Value::keyCompareImplStringish(v1->sv, v2->sv);
        }

    private:
        ASCIIStringValue(const Type* vtype, SourcePos spos, std::string&& sv) : PrimtitiveValue(vtype, spos), sv(std::move(sv)) { ; }
    };

    class ByteBufferValue : public PrimtitiveValue
    {
    public:
        const std::vector<uint8_t> bytes;

        virtual ~ByteBufferValue() = default;

        static uint8_t extractByteValue(char hb, char lb);
        static ByteBufferValue* createFromParse(const Type* vtype, SourcePos spos, const char* chars);

        virtual std::string toString() const override
        {
            return "0x[" + std::string(this->bytes.begin(), this->bytes.end()) + "]";
        }

    private:
        ByteBufferValue(const Type* vtype, SourcePos spos, std::vector<uint8_t> bytes) : PrimtitiveValue(vtype, spos), bytes(bytes) { ; }
    };

    class UUIDv4Value : public PrimtitiveValue 
    {
    public:
        //TODO: this is currently the uuid as a string -- is the byte representation more useful?
        const std::string uuidstr;
    
        UUIDv4Value(const Type* vtype, SourcePos spos, std::string uuidstr) : PrimtitiveValue(vtype, spos), uuidstr(uuidstr) { ; }
        virtual ~UUIDv4Value() = default;

        virtual std::string toString() const override
        {
            return std::string("uuid4{") + this->uuidstr + "}";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const UUIDv4Value* v1, const UUIDv4Value* v2)
        {
            return Value::keyCompareImplStringish(v1->uuidstr, v2->uuidstr);
        }
    };

    class UUIDv7Value : public PrimtitiveValue 
    {
    public:
        //TODO: this is currently the uuid as a string -- is the byte representation more useful?
        const std::string uuidstr;
    
        UUIDv7Value(const Type* vtype, SourcePos spos, std::string uuidstr) : PrimtitiveValue(vtype, spos), uuidstr(uuidstr) { ; }
        virtual ~UUIDv7Value() = default;

        virtual std::string toString() const override
        {
            return std::string("uuid7{") + this->uuidstr + "}";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const UUIDv7Value* v1, const UUIDv7Value* v2)
        {
            return Value::keyCompareImplStringish(v1->uuidstr, v2->uuidstr);
        }
    };

    class SHAContentHashValue : public PrimtitiveValue 
    {
    public:
        //TODO: this is currently the hashcode as a string -- is the byte representation more useful?
        const std::string hashstr;
    
        SHAContentHashValue(const Type* vtype, SourcePos spos, std::string hashstr) : PrimtitiveValue(vtype, spos), hashstr(hashstr) { ; }
        virtual ~SHAContentHashValue() = default;

        virtual std::string toString() const override
        {
            return std::string("sha3") + "{" + this->hashstr + "}";
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const SHAContentHashValue* v1, const SHAContentHashValue* v2)
        {
            return Value::keyCompareImplStringish(v1->hashstr, v2->hashstr);
        }
    };

    class DateTimeValue : public PrimtitiveValue 
    {
    public:
        const DateTime tv;
    
        DateTimeValue(const Type* vtype, SourcePos spos, DateTime tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~DateTimeValue() = default;

        virtual std::string toString() const override
        {
            char buf[64];
            sprintf(buf, "%.4u-%.2u-%.2uT%.2u:%.2u:%.2u{%s}", this->tv.year, this->tv.month, this->tv.day, this->tv.hour, this->tv.min, this->tv.sec, this->tv.tzdata);
            
            return std::string(buf);
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }
    };

    class UTCDateTimeValue : public PrimtitiveValue 
    {
    public:
        const UTCDateTime tv;
    
        UTCDateTimeValue(const Type* vtype, SourcePos spos, UTCDateTime tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~UTCDateTimeValue() = default;

        virtual std::string toString() const override
        {
            char buf[64];
            sprintf(buf, "%.4u-%.2u-%.2uT%.2u:%.2u:%.2uZ", this->tv.year, this->tv.month, this->tv.day, this->tv.hour, this->tv.min, this->tv.sec);
            
            return std::string(buf);
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const UTCDateTimeValue* v1, const UTCDateTimeValue* v2)
        {
            uint16_t v1vs[6] = {v1->tv.year, v1->tv.month, v1->tv.day, v1->tv.hour, v1->tv.min, v1->tv.sec};
            uint16_t v2vs[6] = {v2->tv.year, v2->tv.month, v2->tv.day, v2->tv.hour, v2->tv.min, v2->tv.sec};

            return Value::keyCompareImplArray(v1vs, v2vs, 6);
        }
    };

    class PlainDateValue : public PrimtitiveValue 
    {
    public:
        const PlainDate tv;
    
        PlainDateValue(const Type* vtype, SourcePos spos, PlainDate tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~PlainDateValue() = default;

        virtual std::string toString() const override
        {
            char buf[64];
            sprintf(buf, "%.4u-%.2u-%.2u", this->tv.year, this->tv.month, this->tv.day);
            
            return std::string(buf);
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const PlainDateValue* v1, const PlainDateValue* v2)
        {
            uint16_t v1vs[3] = {v1->tv.year, v1->tv.month, v1->tv.day};
            uint16_t v2vs[3] = {v2->tv.year, v2->tv.month, v2->tv.day};

            return Value::keyCompareImplArray(v1vs, v2vs, 3);
        }
    };

    class PlainTimeValue : public PrimtitiveValue 
    {
    public:
        const PlainTime tv;
    
        PlainTimeValue(const Type* vtype, SourcePos spos, PlainTime tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~PlainTimeValue() = default;

        virtual std::string toString() const override
        {
            char buf[64];
            sprintf(buf, "%.2u:%.2u:%.2u", this->tv.hour, this->tv.min, this->tv.sec);
            
            return std::string(buf);
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const PlainTimeValue* v1, const PlainTimeValue* v2)
        {
            uint16_t v1vs[3] = {v1->tv.hour, v1->tv.min, v1->tv.sec};
            uint16_t v2vs[3] = {v2->tv.hour, v2->tv.min, v2->tv.sec};

            return Value::keyCompareImplArray(v1vs, v2vs, 3);
        }
    };

    class LogicalTimeValue : public PrimtitiveValue 
    {
    public:
        const uint64_t tv;
    
        LogicalTimeValue(const Type* vtype, SourcePos spos, uint64_t tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~LogicalTimeValue() = default;

        virtual std::string toString() const override
        {
            return std::to_string(this->tv);
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const LogicalTimeValue* v1, const LogicalTimeValue* v2)
        {
            return Value::keyCompareImplScalars(v1->tv, v2->tv);
        }
    };

    class TickTimeValue : public PrimtitiveValue 
    {
    public:
        const uint64_t tv;
    
        TickTimeValue(const Type* vtype, SourcePos spos, uint64_t tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~TickTimeValue() = default;

        virtual std::string toString() const override
        {
            return std::to_string(this->tv);
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const TickTimeValue* v1, const TickTimeValue* v2)
        {
            return Value::keyCompareImplScalars(v1->tv, v2->tv);
        }
    };

    class ISOTimeStampValue : public PrimtitiveValue 
    {
    public:
        const ISOTimeStamp tv;
    
        ISOTimeStampValue(const Type* vtype, SourcePos spos, ISOTimeStamp tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~ISOTimeStampValue() = default;

        virtual std::string toString() const override
        {
            char buf[64];
            sprintf(buf, "%.4u-%.2u-%.2uT%.2u:%.2u:%.2u.%.3uZ", this->tv.year, this->tv.month, this->tv.day, this->tv.hour, this->tv.min, this->tv.sec, this->tv.millis);
            
            return std::string(buf);
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const ISOTimeStampValue* v1, const ISOTimeStampValue* v2)
        {
            uint16_t v1vs[7] = {v1->tv.year, v1->tv.month, v1->tv.day, v1->tv.hour, v1->tv.min, v1->tv.sec, v1->tv.millis};
            uint16_t v2vs[7] = {v2->tv.year, v2->tv.month, v2->tv.day, v2->tv.hour, v2->tv.min, v2->tv.sec, v2->tv.millis};

            return Value::keyCompareImplArray(v1vs, v2vs, 7);
        }
    };

    class RegexValue : public PrimtitiveValue 
    {
    public:
        //This is a bit tricky as we map from the string in the BSQON format to the statically declared regex in the assembly.
        //TODO: we should normalize this (by parsing and then formatting) to eliminate any simple differences (although we are not going to do regex equality)
        const BSQRegex* tv;
    
        RegexValue(const Type* vtype, SourcePos spos, BSQRegex* tv) : PrimtitiveValue(vtype, spos), tv(tv) { ; }
        virtual ~RegexValue() = default;

        virtual std::string toString() const override
        {
            return this->tv->toString();
        }
    };

    class StringOfValue : public Value
    {
    public:
        const UnicodeString sv;

        virtual ~StringOfValue() = default;

        //null if validator fails
        static StringOfValue* createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length, const BSQRegex* validator);

        virtual std::string toString() const override
        {
            auto ustr = escapeString(this->sv);
            return "\"" + std::string(ustr.begin(), ustr.end()) + "\"" + this->vtype->tkey;
        }

        const StringOfType* getStringOfType() const
        {
            return (const StringOfType*)this->vtype;
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const StringOfValue* v1, const StringOfValue* v2)
        {
            return Value::keyCompareImplStringish(v1->sv, v2->sv);
        }

    private:
        StringOfValue(const Type* vtype, SourcePos spos, UnicodeString&& sv) : Value(vtype, spos), sv(std::move(sv)) { ; }
    };

    class ASCIIStringOfValue : public Value
    {
    public:
        const std::string sv;

        virtual ~ASCIIStringOfValue() = default;

        //null if validator fails
        static ASCIIStringOfValue* createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length, const BSQRegex* validator);

        virtual std::string toString() const override
        {
            auto ustr = escapeASCIIString(this->sv);
            return "'" + std::string(ustr.begin(), ustr.end()) + "'";
        }

        const ASCIIStringOfType* getASCIIStringOfType() const
        {
            return (const ASCIIStringOfType*)this->vtype;
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const ASCIIStringOfValue* v1, const ASCIIStringOfValue* v2)
        {
            return Value::keyCompareImplStringish(v1->sv, v2->sv);
        }

    private:
        ASCIIStringOfValue(const Type* vtype, SourcePos spos, std::string&& sv) : Value(vtype, spos), sv(std::move(sv)) { ; }
    };

    class SomethingValue : public Value
    {
    public:
        const Value* v;

        SomethingValue(const Type* vtype, SourcePos spos, const Value* v) : Value(vtype, spos), v(v) { ; }
        virtual ~SomethingValue() = default;

        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + this->v->toString() + "}";
        }

        const SomethingType* getSomethingType() const
        {
            return (const SomethingType*)this->vtype;
        }
    };

    class OkValue : public Value
    {
    public:
        const Value* v;

        OkValue(const Type* vtype, SourcePos spos, const Value* v) : Value(vtype, spos), v(v) { ; }
        virtual ~OkValue() = default;

        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + this->v->toString() + "}";
        }

        const OkType* getOkType() const
        {
            return (const OkType*)this->vtype;
        }
    };

    class ErrValue : public Value
    {
    public:
        const Value* v;

        ErrValue(const Type* vtype, SourcePos spos, const Value* v) : Value(vtype, spos), v(v) { ; }
        virtual ~ErrValue() = default;

        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + this->v->toString() + "}";
        }

        const ErrorType* getErrType() const
        {
            return (const ErrorType*)this->vtype;
        }
    };

    class PathValue : public Value
    {
    public:
        const std::string sv;

        virtual ~PathValue() = default;

        //null if validator fails
        static PathValue* createFromParse(const Type* vtype, SourcePos spos, const uint8_t* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathType* getPathType() const
        {
            return (const PathType*)this->vtype;
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const PathValue* v1, const PathValue* v2)
        {
            return Value::keyCompareImplStringish(v1->sv, v2->sv);
        }

    private:
        PathValue(const Type* vtype, SourcePos spos, std::string&& sv) : Value(vtype, spos), sv(std::move(sv)) { ; }
    };

    class PathFragmentValue : public Value
    {
    public:
        const std::string sv;

        virtual ~PathFragmentValue() = default;

        //null if validator fails
        static PathFragmentValue* createFromParse(const Type* vtype, SourcePos spos, const uint8_t* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "f`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathFragmentType* getPathFragmentType() const
        {
            return (const PathFragmentType*)this->vtype;
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const PathFragmentValue* v1, const PathFragmentValue* v2)
        {
            return Value::keyCompareImplStringish(v1->sv, v2->sv);
        }

    private:
        PathFragmentValue(const Type* vtype, SourcePos spos, std::string&& sv) : Value(vtype, spos), sv(std::move(sv)) { ; }
    };

    class PathGlobValue : public Value
    {
    public:
        const std::string sv;

        virtual ~PathGlobValue() = default;

        //null if validator fails
        static PathGlobValue* createFromParse(const Type* vtype, SourcePos spos, const uint8_t* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "g`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathGlobType* getPathGlobType() const
        {
            return (const PathGlobType*)this->vtype;
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const PathGlobValue* v1, const PathGlobValue* v2)
        {
            return Value::keyCompareImplStringish(v1->sv, v2->sv);
        }

    private:
        PathGlobValue(const Type* vtype, SourcePos spos, std::string&& sv) : Value(vtype, spos), sv(std::move(sv)) { ; }
    };

    class ListValue : public Value
    {
    public:
        const std::vector<Value*> vals;

        ListValue(const Type* vtype, SourcePos spos, std::vector<Value*>&& vals) : Value(vtype, spos), vals(std::move(vals)) { ; }
        virtual ~ListValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : std::move(a) + ", ") + v->toString(); }) + "}";
        }

        const ListType* getListType() const
        {
            return (const ListType*)this->vtype;
        }
    };

    class StackValue : public Value
    {
    public:
        const std::vector<Value*> vals;

        StackValue(const Type* vtype, SourcePos spos, std::vector<Value*>&& vals) : Value(vtype, spos), vals(std::move(vals)) { ; }
        virtual ~StackValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : std::move(a) + ", ") + v->toString(); }) + "}";
        }

        const StackType* getStackType() const
        {
            return (const StackType*)this->vtype;
        }
    };

    class QueueValue : public Value
    {
    public:
        const std::vector<Value*> vals;

        QueueValue(const Type* vtype, SourcePos spos, std::vector<Value*>&& vals) : Value(vtype, spos), vals(std::move(vals)) { ; }
        virtual ~QueueValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : std::move(a) + ", ") + v->toString(); }) + "}";
        }

        const QueueType* getQueueType() const
        {
            return (const QueueType*)this->vtype;
        }
    };

    class SetValue : public Value
    {
    public:
        const std::vector<Value*> vals;

        SetValue(const Type* vtype, SourcePos spos, std::vector<Value*>&& vals) : Value(vtype, spos), vals(std::move(vals)) { ; }
        virtual ~SetValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : std::move(a) + ", ") + v->toString(); }) + "}";
        }

        const SetType* getSetType() const
        {
            return (const SetType*)this->vtype;
        }
    };

    class MapEntryValue : public Value
    {
    public:
        const Value* key;
        const Value* val;

        MapEntryValue(const Type* vtype, SourcePos spos, const Value* key, const Value* val) : Value(vtype, spos), key(key), val(val) { ; }
        virtual ~MapEntryValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + this->key->toString() + " -> " + this->val->toString() + "}";
        }

        const MapEntryType* getMapEntryType() const
        {
            return (const MapEntryType*)this->vtype;
        }
    };

    class MapValue : public Value
    {
    public:
        const std::vector<MapEntryValue*> vals;

        MapValue(const Type* vtype, SourcePos spos, std::vector<MapEntryValue*>&& vals) : Value(vtype, spos), vals(std::move(vals)) { ; }
        virtual ~MapValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const MapEntryValue* v) { return (a == "" ? "" : std::move(a) + ", ") + v->toString(); }) + "}";
        }

        const MapType* getMapType() const
        {
            return (const MapType*)this->vtype;
        }
    };

    class EnumValue : public Value
    {
    public:
        const std::string evname;
        const uint32_t ev;

        EnumValue(const Type* vtype, SourcePos spos, std::string evname, uint32_t ev) : Value(vtype, spos), evname(evname), ev(ev) { ; }
        virtual ~EnumValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "::" + this->evname;
        }

        const EnumType* getEnumType() const
        {
            return (const EnumType*)this->vtype;
        }

        virtual bool isValidForTypedecl() const override
        {
            return true;
        }

        static int keyCompare(const EnumValue* v1, const EnumValue* v2)
        {
            return Value::keyCompareImplScalars(v1->ev, v2->ev);
        }
    };

    class TypedeclValue : public Value
    {
    public:
        const Value* basevalue;

        TypedeclValue(const Type* vtype, SourcePos spos, const Value* basevalue) : Value(vtype, spos), basevalue(basevalue) { ; }
        virtual ~TypedeclValue() = default;
        
        virtual std::string toString() const override
        {
            return this->basevalue->toString() + "_" + this->vtype->tkey;
        }

        const TypedeclType* getTypedeclType() const
        {
            return (const TypedeclType*)this->vtype;
        }
    };

    class EntityValue : public Value
    {
    public:
        //value is nullptr if we need to use the default constructor
        const std::vector<Value*> fieldvalues;

        EntityValue(const Type* vtype, SourcePos spos, const std::vector<Value*>&& fieldvalues) : Value(vtype, spos), fieldvalues(std::move(fieldvalues)) { ; }
        virtual ~EntityValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->fieldvalues.begin(), this->fieldvalues.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : std::move(a) + ", ") + (v != nullptr ? v->toString() : "^DEFAULT_INITIALIZER^"); }) + "}";
        }

        const EntityType* getEntityType() const
        {
            return (const EntityType*)this->vtype;
        }
    };

    class TupleValue : public Value
    {
    public:
        const std::vector<Value*> values;

        TupleValue(const Type* vtype, SourcePos spos, const std::vector<Value*>&& values) : Value(vtype, spos), values(std::move(values)) { ; }
        virtual ~TupleValue() = default;
        
        virtual std::string toString() const override
        {
            return "<" + this->vtype->tkey + ">[" + std::accumulate(this->values.begin(), this->values.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : std::move(a) + ", ") + v->toString(); }) + "]";
        }

        const TupleType* getTupleType() const
        {
            return (const TupleType*)this->vtype;
        }
    };

    class RecordValue : public Value
    {
    public:
        const std::vector<Value*> values;

        RecordValue(const Type* vtype, SourcePos spos, const std::vector<Value*>&& values) : Value(vtype, spos), values(std::move(values)) { ; }
        virtual ~RecordValue() = default;
        
        virtual std::string toString() const override
        {
            return "<" + this->vtype->tkey + ">{" + std::accumulate(this->values.begin(), this->values.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : std::move(a) + ", ") + v->toString(); }) + "}";
        }

        const RecordType* getRecordType() const
        {
            return (const RecordType*)this->vtype;
        }
    };

    class EListValue : public Value
    {
    public:
        const std::vector<Value*> values;

        EListValue(const Type* vtype, SourcePos spos, const std::vector<Value*>&& values) : Value(vtype, spos), values(std::move(values)) { ; }
        virtual ~EListValue() = default;
        
        virtual std::string toString() const override
        {
            return "(|" + std::accumulate(this->values.begin(), this->values.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : std::move(a) + ", ") + v->toString(); }) + "|)";
        }

        const EListType* getEListType() const
        {
            return (const EListType*)this->vtype;
        }
    };

    class IdentifierValue : public Value
    {
    public:
        const std::string vname;

        IdentifierValue(const Type* vtype, SourcePos spos, std::string vname) : Value(vtype, spos), vname(vname) { ; }
        virtual ~IdentifierValue() = default;

        virtual std::string toString() const override
        {
            return vname;
        }
    };

    class LetInValue : public Value
    {
    public:
        const std::string vname;
        const Type* oftype;
        const Value* value;
        const Value* exp;

        LetInValue(const Type* vtype, SourcePos spos, std::string vname, const Type* oftype, const Value* value, const Value* exp) : Value(vtype, spos), vname(vname), oftype(oftype), value(value), exp(exp) { ; }
        virtual ~LetInValue() = default;

        virtual std::string toString() const override
        {
            return "(let " + this->vname + ": " + this->oftype->tkey + " = " + this->value->toString() + " in " + this->exp->toString() + ")";
        }
    };
}
