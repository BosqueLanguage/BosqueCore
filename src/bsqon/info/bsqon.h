#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"
#include "../regex/bsqpath.h"
#include "type_info.h"

namespace BSQON
{
    class Value
    {
    public:
        const Type* vtype;

        Value(const Type* vtype) : vtype(vtype) { ; }
        virtual ~Value() = default;

        virtual std::string toString() const = 0;
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

        virtual std::string toString() const override
        {
            return "none";
        }
    };

    class NothingValue : public PrimtitiveValue 
    {
    public:
        NothingValue(const Type* vtype) : PrimtitiveValue(vtype) { ; }
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
    
        BoolValue(const Type* vtype, bool tv) : PrimtitiveValue(vtype), tv(tv) { ; }
        virtual ~BoolValue() = default;

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        virtual std::string toString() const override
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

        OkValue(const Type* vtype, const Value* v) : Value(vtype), v(v) { ; }
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

        ErrValue(const Type* vtype, const Value* v) : Value(vtype), v(v) { ; }
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
        static PathValue* createFromParse(const Type* vtype, const char* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathType* getPathType() const
        {
            return (const PathType*)this->vtype;
        }

    private:
        PathValue(const Type* vtype, std::string&& sv) : Value(vtype), sv(std::move(sv)) { ; }
    };

    class PathFragmentValue : public Value
    {
    public:
        const std::string sv;

        virtual ~PathFragmentValue() = default;

        //null if validator fails
        static PathFragmentValue* createFromParse(const Type* vtype, const char* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "f`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathFragmentType* getPathFragmentType() const
        {
            return (const PathFragmentType*)this->vtype;
        }

    private:
        PathFragmentValue(const Type* vtype, std::string&& sv) : Value(vtype), sv(std::move(sv)) { ; }
    };

    class PathGlobValue : public Value
    {
    public:
        const std::string sv;

        virtual ~PathGlobValue() = default;

        //null if validator fails
        static PathGlobValue* createFromParse(const Type* vtype, const char* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "g`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathGlobType* getPathGlobType() const
        {
            return (const PathGlobType*)this->vtype;
        }

    private:
        PathGlobValue(const Type* vtype, std::string&& sv) : Value(vtype), sv(std::move(sv)) { ; }
    };

    class ListValue : public Value
    {
    public:
        const std::vector<Value*> vals;

        ListValue(const Type* vtype, std::vector<Value*>&& vals) : Value(vtype), vals(std::move(vals)) { ; }
        virtual ~ListValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : a + ", ") + v->toString(); }) + "}";
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

        StackValue(const Type* vtype, std::vector<Value*>&& vals) : Value(vtype), vals(std::move(vals)) { ; }
        virtual ~StackValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : a + ", ") + v->toString(); }) + "}";
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

        QueueValue(const Type* vtype, std::vector<Value*>&& vals) : Value(vtype), vals(std::move(vals)) { ; }
        virtual ~QueueValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : a + ", ") + v->toString(); }) + "}";
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

        SetValue(const Type* vtype, std::vector<Value*>&& vals) : Value(vtype), vals(std::move(vals)) { ; }
        virtual ~SetValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : a + ", ") + v->toString(); }) + "}";
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

        MapEntryValue(const Type* vtype, const Value* key, const Value* val) : Value(vtype), key(key), val(val) { ; }
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

        MapValue(const Type* vtype, std::vector<MapEntryValue*>&& vals) : Value(vtype), vals(std::move(vals)) { ; }
        virtual ~MapValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->vals.begin(), this->vals.end(), std::string(), [](std::string&& a, const MapEntryValue* v) { return (a == "" ? "" : a + ", ") + v->toString(); }) + "}";
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

        EnumValue(const Type* vtype, std::string evname, uint32_t ev) : Value(vtype), evname(evname), ev(ev) { ; }
        virtual ~EnumValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "::" + this->evname;
        }

        const EnumType* getEnumType() const
        {
            return (const EnumType*)this->vtype;
        }
    };

    class TypedeclValue : public Value
    {
    public:
        const Value* basevalue;

        TypedeclValue(const Type* vtype, const Value* basevalue) : Value(vtype), basevalue(basevalue) { ; }
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

        EntityValue(const Type* vtype, const std::vector<Value*>&& fieldvalues) : Value(vtype), fieldvalues(std::move(fieldvalues)) { ; }
        virtual ~EntityValue() = default;
        
        virtual std::string toString() const override
        {
            return this->vtype->tkey + "{" + std::accumulate(this->fieldvalues.begin(), this->fieldvalues.end(), std::string(), [](std::string&& a, const Value* v) { return (a == "" ? "" : a + ", ") + (v != nullptr ? v->toString() : "^DEFAULT_INITIALIZER^"); }) + "}";
        }

        const EntityType* getEntityType() const
        {
            return (const EntityType*)this->vtype;
        }
    };
}
