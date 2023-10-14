#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"
#include "type_info.h"

namespace BSQON
{
    class Value
    {
    public:
        const Type* vtype;

        Value(const Type* vtype) : vtype(vtype) { ; }
        virtual ~Value() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const = 0;
    };

    class PrimtitiveValue : public Value
    {
    public:
        PrimtitiveValue(const Type* vtype) : Value(vtype) { ; }
        virtual ~PrimtitiveValue() = default;

        const PrimitiveType* getPrimitiveType() const
        {
            return (const PrimitiveType*)this->vtype;
        }
    };

    class NoneValue : public PrimtitiveValue 
    {
    public:
        NoneValue(const Type* vtype) : PrimtitiveValue(vtype) { ; }
        virtual ~NoneValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return "none";
        }
    };

    class NothingValue : public PrimtitiveValue 
    {
    public:
        NothingValue(const Type* vtype) : PrimtitiveValue(vtype) { ; }
        virtual ~NothingValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return "nothing";
        }
    };

    class BoolValue : public PrimtitiveValue 
    {
    public:
        const bool tv;
    
        BoolValue(const Type* vtype, bool tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~BoolValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return this->tv ? "true" : "false";
        }
    };

    class NatNumberValue : public PrimtitiveValue 
    {
    public:
        const uint64_t cnv;
        const std::string nv;
    
        NatNumberValue(const Type* vtype, uint64_t cnv, std::string nv) : PrimtitiveValue(vtype), cnv(cnv), nv(nv) { ; }
        virtual ~NatNumberValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return this->nv + (this->vtype->tkey == "Nat" ? "n" : "N");
        }
    };

    class IntNumberValue : public PrimtitiveValue 
    {
    public:
        const int64_t cnv;
        const std::string nv;
    
        IntNumberValue(const Type* vtype, int64_t cnv, std::string nv) : PrimtitiveValue(vtype), cnv(cnv), nv(nv) { ; }
        virtual ~IntNumberValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return this->nv + (this->vtype->tkey == "Int" ? "i" : "I");
        }
    };

    class FloatNumberValue : public PrimtitiveValue 
    {
    public:
        const std::string nv;
    
        FloatNumberValue(const Type* vtype, std::string nv) : PrimtitiveValue(vtype), nv(nv) { ; }
        virtual ~FloatNumberValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return this->nv + (this->vtype->tkey == "Float" ? "f" : "d");
        }
    };

    class RationalNumberValue : public PrimtitiveValue 
    {
    public:
        const int64_t ival;
        const std::string numerator;
        const std::string denominator;
    
        RationalNumberValue(const Type* vtype, int64_t ival, std::string numerator, std::string denominator) : PrimtitiveValue(vtype), ival(ival), numerator(numerator), denominator(denominator) { ; }
        virtual ~RationalNumberValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            if(ival == 0) {
                return "0R";
            }
            else {
                return this->numerator + "/" + this->denominator + "R";
            }
        }
    };

    class StringValue : public PrimtitiveValue 
    {
    public:
        const UnicodeString sv;
    
        virtual ~StringValue() = default;

        static StringValue* createFromParse(const Type* vtype, const uint8_t* bytes, size_t length);

        static UnicodeString unescapeString(const uint8_t* bytes, size_t length);
        static std::vector<uint8_t> escapeString(UnicodeString sv);

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            auto ustr = StringValue::escapeString(this->sv);
            return "\"" + std::string(ustr.begin(), ustr.end()) + "\"";
        }

    private:
        StringValue(const Type* vtype, UnicodeString&& sv) : PrimtitiveValue(vtype), sv(std::move(sv)) { ; }
    };

    class ASCIIStringValue : public PrimtitiveValue
    {
    public:
        const std::string sv;
    
        virtual ~ASCIIStringValue() = default;

        static ASCIIStringValue* createFromParse(const Type* vtype, const char* bytes, size_t length);

        static std::string unescapeString(const char* chars, size_t length);
        static std::vector<uint8_t> escapeString(std::string sv);

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            auto ustr = ASCIIStringValue::escapeString(this->sv);
            return "'" + std::string(ustr.begin(), ustr.end()) + "'";
        }

    private:
        ASCIIStringValue(const Type* vtype, std::string&& sv) : PrimtitiveValue(vtype), sv(std::move(sv)) { ; }
    };

    class ByteBufferValue : public PrimtitiveValue
    {
    public:
        const std::vector<uint8_t> bytes;
    
        ByteBufferValue(const Type* vtype, std::vector<uint8_t> bytes) : PrimtitiveValue(vtype), bytes(bytes) { ; }
        virtual ~ByteBufferValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return "0x[" + std::string(this->bytes.begin(), this->bytes.end()) + "]";
        }
    };

    class UUIDValue : public PrimtitiveValue 
    {
    public:
        const std::string uuidstr;
    
        UUIDValue(const Type* vtype, std::string uuidstr) : PrimtitiveValue(vtype), uuidstr(uuidstr) { ; }
        virtual ~UUIDValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return std::string("uuid") + (this->vtype->tkey == "UUIDv4" ? "4" : "7") + "{" + this->uuidstr + "}";
        }
    };

    class SHAContentHashValue : public PrimtitiveValue 
    {
    public:
        const std::string hashstr;
    
        SHAContentHashValue(const Type* vtype, std::string hashstr) : PrimtitiveValue(vtype), hashstr(hashstr) { ; }
        virtual ~SHAContentHashValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return std::string("sha3") + "{" + this->hashstr + "}";
        }
    };

    class DateTimeValue : public PrimtitiveValue 
    {
    public:
        const DateTime tv;
    
        DateTimeValue(const Type* vtype, DateTime tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~DateTimeValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            char buf[64];
            sprintf(buf, "%.4u-%.2u-%.2uT%.2u:%.2u:%.2u{%s}", this->tv.year, this->tv.month, this->tv.day, this->tv.hour, this->tv.min, this->tv.sec, this->tv.tzdata);
            
            return std::string(buf);
        }
    };

    class UTCDateTimeValue : public PrimtitiveValue 
    {
    public:
        const UTCDateTime tv;
    
        UTCDateTimeValue(const Type* vtype, UTCDateTime tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~UTCDateTimeValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            char buf[64];
            sprintf(buf, "%.4u-%.2u-%.2uT%.2u:%.2u:%.2uZ", this->tv.year, this->tv.month, this->tv.day, this->tv.hour, this->tv.min, this->tv.sec);
            
            return std::string(buf);
        }
    };

    class PlainDateValue : public PrimtitiveValue 
    {
    public:
        const PlainDate tv;
    
        PlainDateValue(const Type* vtype, PlainDate tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~PlainDateValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            char buf[64];
            sprintf(buf, "%.4u-%.2u-%.2u", this->tv.year, this->tv.month, this->tv.day);
            
            return std::string(buf);
        }
    };

    class PlainTimeValue : public PrimtitiveValue 
    {
    public:
        const PlainTime tv;
    
        PlainTimeValue(const Type* vtype, PlainTime tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~PlainTimeValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            char buf[64];
            sprintf(buf, "%.2u:%.2u:%.2u", this->tv.hour, this->tv.min, this->tv.sec);
            
            return std::string(buf);
        }
    };

    class LogicalTimeValue : public PrimtitiveValue 
    {
    public:
        const uint64_t tv;
    
        LogicalTimeValue(const Type* vtype, uint64_t tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~LogicalTimeValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return std::to_string(this->tv);
        }
    };

    class TickTimeValue : public PrimtitiveValue 
    {
    public:
        const uint64_t tv;
    
        TickTimeValue(const Type* vtype, uint64_t tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~TickTimeValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return std::to_string(this->tv);
        }
    };

    class ISOTimeStampValue : public PrimtitiveValue 
    {
    public:
        const ISOTimeStamp tv;
    
        ISOTimeStampValue(const Type* vtype, ISOTimeStamp tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~ISOTimeStampValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            char buf[64];
            sprintf(buf, "%.4u-%.2u-%.2uT%.2u:%.2u:%.2u.%.3uZ", this->tv.year, this->tv.month, this->tv.day, this->tv.hour, this->tv.min, this->tv.sec, this->tv.millis);
            
            return std::string(buf);
        }
    };

    class RegexValue : public PrimtitiveValue 
    {
    public:
        const BSQRegex tv;
    
        RegexValue(const Type* vtype, BSQRegex tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~RegexValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            return this->tv.toString();
        }
    };

    class StringOfValue : public Value
    {
    public:
        const UnicodeString sv;

        virtual ~StringOfValue() = default;

        //null if validator fails
        static StringOfValue* createFromParse(const Type* vtype, const uint8_t* bytes, size_t length, const BSQRegex* validator);

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            auto ustr = StringValue::escapeString(this->sv);
            return "\"" + std::string(ustr.begin(), ustr.end()) + "\"" + this->vtype->tkey;
        }

        const StringOfType* getStringOfType() const
        {
            return (const StringOfType*)this->vtype;
        }

    private:
        StringOfValue(const Type* vtype, UnicodeString&& sv) : Value(vtype), sv(std::move(sv)) { ; }
    };

    class ASCIIStringOfValue : public Value
    {
    public:
        const std::string sv;

        virtual ~ASCIIStringOfValue() = default;

        //null if validator fails
        static ASCIIStringOfValue* createFromParse(const Type* vtype, const char* chars, size_t length, const BSQRegex* validator);

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            auto ustr = ASCIIStringValue::escapeString(this->sv);
            return "'" + std::string(ustr.begin(), ustr.end()) + "'";
        }

        const ASCIIStringOfType* getASCIIStringOfType() const
        {
            return (const ASCIIStringOfType*)this->vtype;
        }

    private:
        ASCIIStringOfValue(const Type* vtype, std::string&& sv) : Value(vtype), sv(std::move(sv)) { ; }
    };

    class SomethingValue : public Value
    {
    public:
        const Value* v;

        SomethingValue(const Type* vtype, const Value* v) : Value(vtype), v(v) { ; }
        virtual ~SomethingValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            auto oftype = assembly.resolveType(this->getSomethingType()->oftype);
                
            if(declared->tag == TypeTag::TYPE_SOMETHING || declared->tag == TypeTag::TYPE_OPTION) {
                return "something(" + this->v->toString(oftype, assembly) + ")";
            }
            else {
                return this->vtype->tkey + "{" + this->v->toString(oftype, assembly) + "}";
            }
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

        OkValue(const Type* vtype, const Value* v) : Value(vtype), v(v) { ; }
        virtual ~OkValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            auto oftype = assembly.resolveType(this->getOkType()->ttype);
                
            if(declared->tag == TypeTag::TYPE_OK || declared->tag == TypeTag::TYPE_RESULT) {
                return "ok(" + this->v->toString(oftype, assembly) + ")";
            }
            else {
                return this->vtype->tkey + "{" + this->v->toString(oftype, assembly) + "}";
            }
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

        ErrValue(const Type* vtype, const Value* v) : Value(vtype), v(v) { ; }
        virtual ~ErrValue() = default;

        virtual std::string toString(const Type* declared, const AssemblyInfo assembly) const override
        {
            auto oftype = assembly.resolveType(this->getErrType()->ttype);

            if (declared->tag == TypeTag::TYPE_ERROR || declared->tag == TypeTag::TYPE_RESULT)
            {
                return "err(" + this->v->toString(oftype, assembly) + ")";
            }
            else
            {
                return this->vtype->tkey + "{" + this->v->toString(oftype, assembly) + "}";
            }
        }

        const ErrorType* getErrType() const
        {
            return (const ErrorType*)this->vtype;
        }
    };
}
