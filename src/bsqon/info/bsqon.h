#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"
#include "../regex/bsqpath.h"
#include "type_info.h"

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
    };

    class NatNumberValue : public PrimtitiveValue 
    {
    public:
        const std::optional<uint64_t> cnv;
        const std::string nv;
    
        NatNumberValue(const Type* vtype, SourcePos spos, std::optional<uint64_t> cnv, std::string nv) : PrimtitiveValue(vtype, spos), cnv(cnv), nv(nv) { ; }
        virtual ~NatNumberValue() = default;

        virtual std::string toString() const override
        {
            return this->nv + (this->vtype->tkey == "Nat" ? "n" : "N");
        }
    };

    class IntNumberValue : public PrimtitiveValue 
    {
    public:
        const std::optional<int64_t> cnv;
        const std::string nv;
    
        IntNumberValue(const Type* vtype, SourcePos spos, std::optional<int64_t> cnv, std::string nv) : PrimtitiveValue(vtype, spos), cnv(cnv), nv(nv) { ; }
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
    
        FloatNumberValue(const Type* vtype, SourcePos spos, std::string nv) : PrimtitiveValue(vtype, spos), nv(nv) { ; }
        virtual ~FloatNumberValue() = default;

        virtual std::string toString() const override
        {
            return this->nv + (this->vtype->tkey == "Float" ? "f" : "d");
        }
    };

    class RationalNumberValue : public PrimtitiveValue 
    {
    public:
        const std::string numerator;
        const uint64_t denominator;
    
        RationalNumberValue(const Type* vtype, SourcePos spos, std::string numerator, uint64_t denominator) : PrimtitiveValue(vtype, spos), numerator(numerator), denominator(denominator) { ; }
        virtual ~RationalNumberValue() = default;

        virtual std::string toString() const override
        {
            return this->numerator + "/" + std::to_string(this->denominator) + "R";
        }
    };

    class StringValue : public PrimtitiveValue 
    {
    public:
        const UnicodeString sv;
    
        virtual ~StringValue() = default;

        static StringValue* createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length);

        //Take a utf8 string with escapes and convert to a utf32 string
        static std::optional<UnicodeString> unescapeString(const uint8_t* bytes, size_t length);

        //Convert a utf32 string to a utf8 string with escapes
        static std::vector<uint8_t> escapeString(const UnicodeString& sv);

        virtual std::string toString() const override
        {
            auto ustr = StringValue::escapeString(this->sv);
            return "\"" + std::string(ustr.begin(), ustr.end()) + "\"";
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

        //Take an ascii string with escapes and convert to a true string
        static std::optional<std::string> unescapeString(const uint8_t* bytes, size_t length);

        //Convert an ascii string to a ascii string with escapes
        static std::vector<uint8_t> escapeString(const std::string& sv);

        virtual std::string toString() const override
        {
            auto ustr = ASCIIStringValue::escapeString(this->sv);
            return "'" + std::string(ustr.begin(), ustr.end()) + "'";
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
            auto ustr = StringValue::escapeString(this->sv);
            return "\"" + std::string(ustr.begin(), ustr.end()) + "\"" + this->vtype->tkey;
        }

        const StringOfType* getStringOfType() const
        {
            return (const StringOfType*)this->vtype;
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
            auto ustr = ASCIIStringValue::escapeString(this->sv);
            return "'" + std::string(ustr.begin(), ustr.end()) + "'";
        }

        const ASCIIStringOfType* getASCIIStringOfType() const
        {
            return (const ASCIIStringOfType*)this->vtype;
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
        static PathValue* createFromParse(const Type* vtype, SourcePos spos, const char* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathType* getPathType() const
        {
            return (const PathType*)this->vtype;
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
        static PathFragmentValue* createFromParse(const Type* vtype, SourcePos spos, const char* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "f`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathFragmentType* getPathFragmentType() const
        {
            return (const PathFragmentType*)this->vtype;
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
        static PathGlobValue* createFromParse(const Type* vtype, SourcePos spos, const char* chars, size_t length, const BSQPath* validator);

        virtual std::string toString() const override
        {
            return "g`" + this->sv + "`" + this->vtype->tkey;
        }

        const PathGlobType* getPathGlobType() const
        {
            return (const PathGlobType*)this->vtype;
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
}
