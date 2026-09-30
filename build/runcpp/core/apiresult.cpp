#include "apiresult.h"

#include "integrals.h"

namespace ᐸRuntimeᐳ
{
    XAPIResultData jsonParseToBSQ_APIResultEntityInfo(const TypeInfo* tinfo, const json& j)
    {
        bsq_validate(j.is_object(), "JSON -> BSQ", 0, nullptr, "Expected an object for APIResultEntityInfo");
        
        XUUIDv7 correlationid = XUUIDv7::nil();
        if(j.contains("correlationid")) {
            jsonParseToBSQ_UUIDv7(tinfo, j["correlationid"], &correlationid);
        }

        XUUIDv4 infoid = XUUIDv4::nil();
        if(j.contains("infoid")) {
            jsonParseToBSQ_UUIDv4(tinfo, j["infoid"], &infoid);
        }

        XAPIInfoTag tagid = XAPIInfoTag::Clear;
        if(j.contains("tagid")) {
            jsonParseToBSQ_Nat(tinfo, j["tagid"], reinterpret_cast<uint64_t*>(&tagid));
        }

        const char* tag = nullptr;
        if(j.contains("tag")) {
            assert(false); //We need to intern or lookup these tags somehow
        }

        return XAPIResultData{correlationid, infoid, tagid, tag};
    }

    XAPIResultData parseToBSQ_APIResultEntityInfo(const TypeInfo* tinfo, BAPILexer* lexer)
    {
        if(!lexer->testIsSymbol(',')) {
            return XAPIResultData{XUUIDv7::nil(), XUUIDv4::nil(), XAPIInfoTag::Clear, nullptr};
        }

        lexer->consume();
        XUUIDv7 correlationid;
        parseToBSQ_UUIDv7(tinfo, lexer, &correlationid);

        bsq_validate(lexer->testIsSymbol(','), "Parse -> BSQ", 0, nullptr, "Expected ','");
        lexer->consume();
        XUUIDv4 infoid;
        parseToBSQ_UUIDv4(tinfo, lexer, &infoid);

        bsq_validate(lexer->testIsSymbol(','), "Parse -> BSQ", 0, nullptr, "Expected ','");
        lexer->consume();
        XNat tagidval;
        parseToBSQ_Nat(tinfo, lexer, &tagidval);
        XAPIInfoTag tagid = static_cast<XAPIInfoTag>(tagidval.value);

        const char* tag = nullptr;
        if(lexer->testIsSymbol(',')) {
            lexer->consume();
            assert(false); //We need to intern or lookup these tags somehow
        }

        return XAPIResultData{correlationid, infoid, tagid, tag};
    }

    void bsqToJSON_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, json& j)
    {
        if(data.tagid == XAPIInfoTag::Clear) {
            return;
        }
        else {
            j["correlationid"] = bsqToJSON_UUIDv7(tinfo, &data.correlationid);
            j["infoid"] = bsqToJSON_UUIDv4(tinfo, &data.infoid);

            XNat tagidval{static_cast<int64_t>(data.tagid)};
            j["tagid"] = bsqToJSON_Nat(tinfo, &tagidval);

            if(data.tag != nullptr) {
                assert(false); //We need to intern or lookup these tags somehow
            }
        }
    }

    void bsqToBAPI_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, BSQStreamingBuilder* builder)
    {
        if(data.tagid == XAPIInfoTag::Clear) {
            return;
        }
        else {
            bsqToBAPI_UUIDv7(tinfo, &data.correlationid, builder);
            bsqToBAPI_UUIDv4(tinfo, &data.infoid, builder);

            XNat tagidval{static_cast<int64_t>(data.tagid)};
            bsqToBAPI_Nat(tinfo, &tagidval, builder);
            if(data.tag != nullptr) {
                assert(false); //We need to intern or lookup these tags somehow
            }
        }
    }

    void displayValue_APIResultEntityInnfo(const TypeInfo* tinfo, const XAPIResultData& data, std::ostream& os, std::optional<std::string> indent)
    {
        if(data.tagid == XAPIInfoTag::Clear) {
            return;
        }
        else {
            os << bsqToJSON_UUIDv7(tinfo, &data.correlationid) << ", ";
            os << bsqToJSON_UUIDv4(tinfo, &data.infoid) << ", ";
            XNat tagidval{static_cast<int64_t>(data.tagid)};
            os << bsqToJSON_Nat(tinfo, &tagidval);
            if(data.tag != nullptr) {
                assert(false); //We need to intern or lookup these tags somehow
            }
        }
    }

    void parseToBSQ_APIResultEntity(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        xxxx;
    }

    json bsqToJSON_APIResultEntity(const TypeInfo* tinfo, const void* valptr)
    {
        xxxx;
    }

    void bsqToBAPI_APIResultEntity(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        xxxx;
    }

    void displayValue_APIResultEntity(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        xxxx;
    }
}
