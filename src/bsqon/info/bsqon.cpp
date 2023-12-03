#include "bsqon.h"

namespace BSQON
{
    StringValue* StringValue::createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length)
    {
        auto sv = std::move(unescapeString(bytes, length));
        if(!sv.has_value()) {
            return nullptr;
        }

        return new StringValue(vtype, spos, std::move(sv.value()));
    }

    ASCIIStringValue* ASCIIStringValue::createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length)
    {
        auto sv = std::move(unescapeASCIIString(bytes, length));
        if(!sv.has_value()) {
            return nullptr;
        }

        return new ASCIIStringValue(vtype, spos, std::move(sv.value()));
    }

    uint8_t ByteBufferValue::extractByteValue(char hb, char lb)
    {
        uint8_t h = ('0' <= hb && hb <= '9') ? (hb - '0') : (hb - 'a' + 10);
        uint8_t l = ('0' <= lb && lb <= '9') ? (lb - '0') : (lb - 'a' + 10);

        return (h << 4) | l;
    }

    ByteBufferValue* ByteBufferValue::createFromParse(const Type* vtype, SourcePos spos, const char* chars)
    {
        auto bblen = strlen(chars) - 4; //0x[...]
        
        const char* curr = chars + 3;
        const char* bbend = chars + bblen;

        if(bblen % 2 != 0) {
            return nullptr;
        }

        std::vector<uint8_t> buff;
        buff.reserve(bblen / 2);

        while(curr != bbend) {
            auto hb = *curr++;
            auto lb = *curr++;
            
            uint8_t bv = ByteBufferValue::extractByteValue(hb, lb);
            buff.push_back(bv);
        }

        return new ByteBufferValue(vtype, spos, std::move(buff));
    }

    StringOfValue* StringOfValue::createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length, const BSQRegex* validator)
    {
        auto str = unescapeString(bytes, length);
        if(!str.has_value()) {
            return nullptr;
        }

        return validator->test(&str.value()) ? new StringOfValue(vtype, spos, std::move(str.value())) : nullptr;
    }

    ASCIIStringOfValue* ASCIIStringOfValue::createFromParse(const Type* vtype, SourcePos spos, const uint8_t* bytes, size_t length, const BSQRegex* validator)
    {
        auto str = std::move(unescapeASCIIString(bytes, length));
        if(!str.has_value()) {
            return nullptr;
        }

        return validator->test(&str.value()) ? new ASCIIStringOfValue(vtype, spos, std::move(str.value())) : nullptr;
    }

    PathValue* PathValue::createFromParse(const Type* vtype, SourcePos spos, const uint8_t* chars, size_t length, const BSQPath* validator)
    {
        auto str = std::move(unescapeASCIIString(chars, length));
        if(!str.has_value()) {
            return nullptr;
        }

        return validator->test(str.value()) ? new PathValue(vtype, spos, std::move(str.value())) : nullptr;
    }

    PathFragmentValue* PathFragmentValue::createFromParse(const Type* vtype, SourcePos spos, const uint8_t* chars, size_t length, const BSQPath* validator)
    {
        //skip the leading 'f'
        auto str = std::move(unescapeASCIIString(chars + 1, length - 1));
        if(!str.has_value()) {
            return nullptr;
        }

        return validator->test(str.value()) ? new PathFragmentValue(vtype, spos, std::move(str.value())) : nullptr;
    }

    PathGlobValue* PathGlobValue::createFromParse(const Type* vtype, SourcePos spos, const uint8_t* chars, size_t length, const BSQPath* validator)
    {
        //skip the leading 'g'
        auto str = std::move(unescapeASCIIString(chars + 1, length - 1));
        if(!str.has_value()) {
            return nullptr;
        }

        return validator->test(str.value()) ? new PathGlobValue(vtype, spos, std::move(str.value())) : nullptr;
    }

    std::vector<TypeKey> s_known_key_order = {
        "None",
        "Bool",
        "Nat",
        "Int",
        "BigNat",
        "BigInt",
        "String",
        "ASCIIString",
        "UTCDateTime",
        "PlainDate",
        "PlainTime",
        "TickTime",
        "LogicalTime",
        "ISOTimeStamp",
        "UUIDv4",
        "UUIDv7",
        "SHAContentHash"
    };

    int Value::keyCompare(const Value* v1, const Value* v2)
    {
        if(v1->vtype->tkey != v2->vtype->tkey) {
            auto iter1 = std::find(s_known_key_order.cbegin(), s_known_key_order.cend(), v1->vtype->tkey);
            auto iter2 = std::find(s_known_key_order.cbegin(), s_known_key_order.cend(), v2->vtype->tkey);

            if(iter1 == s_known_key_order.cend() && iter2 == s_known_key_order.cend()) {
                return (v1->vtype->tkey < v2->vtype->tkey) ? -1 : 1;
            }
            else if (iter1 == s_known_key_order.cend()) {
                return 1;
            }
            else if (iter2 == s_known_key_order.cend()) {
                return -1;
            }
            else {
                return iter1 < iter2 ? -1 : 1;
            }
        }
        else {
            const std::string dtype = v1->vtype->tkey;

            if(v1->vtype->tag == TypeTag::TYPE_PRIMITIVE) {
                if(dtype == "None") {
                    return false;
                }
                else if(dtype == "Bool") {
                    return BoolValue::keyCompare(static_cast<const BoolValue*>(v1), static_cast<const BoolValue*>(v2));
                }
                else if(dtype == "Nat") {
                    return NatNumberValue::keyCompare(static_cast<const NatNumberValue*>(v1), static_cast<const NatNumberValue*>(v2));
                }
                else if(dtype == "Int") {
                    return IntNumberValue::keyCompare(static_cast<const IntNumberValue*>(v1), static_cast<const IntNumberValue*>(v2));
                }
                else if(dtype == "BigNat") {
                    return BigNatNumberValue::keyCompare(static_cast<const BigNatNumberValue*>(v1), static_cast<const BigNatNumberValue*>(v2));
                }
                else if(dtype == "BigInt") {
                    return BigIntNumberValue::keyCompare(static_cast<const BigIntNumberValue*>(v1), static_cast<const BigIntNumberValue*>(v2));
                }
                else if(dtype == "String") {
                    return StringValue::keyCompare(static_cast<const StringValue*>(v1), static_cast<const StringValue*>(v2));
                }
                else if(dtype == "ASCIIString") {
                    return ASCIIStringValue::keyCompare(static_cast<const ASCIIStringValue*>(v1), static_cast<const ASCIIStringValue*>(v2));
                }
                else if(dtype == "UUIDv4") {
                    return UUIDv4Value::keyCompare(static_cast<const UUIDv4Value*>(v1), static_cast<const UUIDv4Value*>(v2));
                }
                else if(dtype == "UUIDv7") {
                    return UUIDv7Value::keyCompare(static_cast<const UUIDv7Value*>(v1), static_cast<const UUIDv7Value*>(v2));
                }
                else if(dtype == "SHAContentHash") {
                    return SHAContentHashValue::keyCompare(static_cast<const SHAContentHashValue*>(v1), static_cast<const SHAContentHashValue*>(v2));
                }
                else if(dtype == "UTCDateTime") {
                    return UTCDateTimeValue::keyCompare(static_cast<const UTCDateTimeValue*>(v1), static_cast<const UTCDateTimeValue*>(v2));
                }
                else if(dtype == "PlainDate") {
                    return PlainDateValue::keyCompare(static_cast<const PlainDateValue*>(v1), static_cast<const PlainDateValue*>(v2));
                }
                else if(dtype == "PlainTime") {
                    return PlainTimeValue::keyCompare(static_cast<const PlainTimeValue*>(v1), static_cast<const PlainTimeValue*>(v2));
                }
                else if(dtype == "TickTime") {
                    return TickTimeValue::keyCompare(static_cast<const TickTimeValue*>(v1), static_cast<const TickTimeValue*>(v2));
                }
                else if(dtype == "LogicalTime") {
                    return LogicalTimeValue::keyCompare(static_cast<const LogicalTimeValue*>(v1), static_cast<const LogicalTimeValue*>(v2));
                }
                else {
                    //should be ISOTimestamp
                    return ISOTimeStampValue::keyCompare(static_cast<const ISOTimeStampValue*>(v1), static_cast<const ISOTimeStampValue*>(v2));
                }
            }
            else {
                switch (v1->vtype->tag)
                {
                case TypeTag::TYPE_ENUM:
                    return EnumValue::keyCompare(static_cast<const EnumValue*>(v1), static_cast<const EnumValue*>(v2));
                case TypeTag::TYPE_STRING_OF:
                    return StringOfValue::keyCompare(static_cast<const StringOfValue*>(v1), static_cast<const StringOfValue*>(v2));
                case TypeTag::TYPE_ASCII_STRING_OF:
                    return ASCIIStringOfValue::keyCompare(static_cast<const ASCIIStringOfValue*>(v1), static_cast<const ASCIIStringOfValue*>(v2));
                case TypeTag::TYPE_PATH:
                    return PathValue::keyCompare(static_cast<const PathValue*>(v1), static_cast<const PathValue*>(v2));
                case TypeTag::TYPE_PATH_FRAGMENT:
                    return PathFragmentValue::keyCompare(static_cast<const PathFragmentValue*>(v1), static_cast<const PathFragmentValue*>(v2));
                case TypeTag::TYPE_PATH_GLOB:
                    return PathGlobValue::keyCompare(static_cast<const PathGlobValue*>(v1), static_cast<const PathGlobValue*>(v2));
                default:
                    //it must be a typedecl
                    return Value::keyCompare(static_cast<const TypedeclValue*>(v1)->basevalue, static_cast<const TypedeclValue*>(v2)->basevalue);
                }
            }
        }
    }
}

