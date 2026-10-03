#include "apiresult.h"

namespace ᐸRuntimeᐳ
{
    XAPIResultData jsonParseToBSQ_APIResultEntityInfo(const TypeInfo* tinfo, const json& j)
    {
        bsq_validate(j.is_object(), "JSON -> BSQ", 0, nullptr, "Expected an object for APIResultEntityInfo");
        
        XAPIInfoTag tagid = XAPIInfoTag::Clear;
        if(j.contains("tagid")) {
            jsonParseToBSQ_Nat(tinfo, j["tagid"], reinterpret_cast<uint64_t*>(&tagid));
        }

        XUUIDv4 infoid = XUUIDv4::nil();
        if(j.contains("infoid")) {
            jsonParseToBSQ_UUIDv4(tinfo, j["infoid"], &infoid);
        }

        const char* tag = nullptr;
        if(j.contains("tag")) {
            assert(false); //We need to intern or lookup these tags somehow
        }

        return XAPIResultData{tagid, infoid, tag};
    }

    XAPIResultData parseToBSQ_APIResultEntityInfo(const TypeInfo* tinfo, BAPILexer* lexer)
    {
        bsq_validate(lexer->testIsSymbol(','), "Parse -> BSQ", 0, nullptr, "Expected ','");
        lexer->consume();
        XNat tagidval;
        parseToBSQ_Nat(tinfo, lexer, &tagidval);
        XAPIInfoTag tagid = static_cast<XAPIInfoTag>(tagidval.value);

        if(tagid == XAPIInfoTag::Clear) {
            return XAPIResultData{tagid, XUUIDv4::nil(), nullptr};
        }
        else {
            bsq_validate(lexer->testIsSymbol(','), "Parse -> BSQ", 0, nullptr, "Expected ','");
            lexer->consume();
            XUUIDv4 infoid;
            parseToBSQ_UUIDv4(tinfo, lexer, &infoid);

            const char* tag = nullptr;
            if(lexer->testIsSymbol(',')) {
                lexer->consume();
                assert(false); //We need to intern or lookup these tags somehow
            }

            return XAPIResultData{tagid, infoid, tag};
        }
    }

    void bsqToJSON_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, json& j)
    {
        if(data.tagid == XAPIInfoTag::Clear) {
            return;
        }
        else {
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
            bsqToBAPI_UUIDv4(tinfo, &data.infoid, builder);

            XNat tagidval{static_cast<int64_t>(data.tagid)};
            bsqToBAPI_Nat(tinfo, &tagidval, builder);
            if(data.tag != nullptr) {
                assert(false); //We need to intern or lookup these tags somehow
            }
        }
    }

    void displayValue_APIResultEntityInfo(const TypeInfo* tinfo, const XAPIResultData& data, std::ostream& os, std::optional<std::string> indent)
    {
        if(data.tagid == XAPIInfoTag::Clear) {
            return;
        }
        else {
            os << bsqToJSON_UUIDv4(tinfo, &data.infoid) << ", ";
            XNat tagidval{static_cast<int64_t>(data.tagid)};
            os << bsqToJSON_Nat(tinfo, &tagidval);
            if(data.tag != nullptr) {
                assert(false); //We need to intern or lookup these tags somehow
            }
        }
    }
}
