#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "uuids.h"

namespace ᐸRuntimeᐳ
{
    enum class XAPIInfoTag : uint64_t
    {
        Clear = 0,
        Timeout = 1,
        Cancelled = 2,
        AccessDenied = 3,
        Error = 4
    };

    class XAPIResultData
    {
    public:
        XUUIDv7 correlationid;
        XUUIDv4 infoid;

        XAPIInfoTag tagid;
        const char* tag; //Type::id format to correlate ad-hoc
    };
    static_assert(sizeof(XAPIResultData) == 48, "Need to update values in compiler");

    enum class XAPIResultKind
    {
        Error,
        Rejected,
        Denied,
        Dropped,
        Success
    };

    template <typename T, XAPIResultKind K>
    class XAPIResultEntityValue
    {
    public:
        XAPIResultData data;
        T value;
    };

    template<typename T>
    void jsonParseToBSQ_APIResultEntity(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array() && j.size() == 2, "JSON -> BSQ", 0, nullptr, "Expected JSON envelope for APIResult<T>");
        bsq_validate(j[0] == "success" || j[0] == tinfo->typekey, "JSON -> BSQ", 0, nullptr, "Full type in JSON envelope for APIResult<T>");

        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        T val;
        ofinfo->opdispatch.jsonParseToBSQFp(ofinfo, j[1], &val);

        xxxx;
        *(XAPIResultEntityValue<T, XAPIResultKind::Success>*)resptr = XAPIResultEntityValue<T, XAPIResultKind::Success>{XAPIResultData{XUUIDv7::nil(), XUUIDv4::nil(), XAPIInfoTag::Clear, nullptr}, val};
    }

    void parseToBSQ_APIResultEntity(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr);
    json bsqToJSON_APIResultEntity(const TypeInfo* tinfo, const void* valptr);
    void bsqToBAPI_APIResultEntity(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder);
    void displayValue_APIResultEntity(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent);

    template<ConceptUnionRepr U>
    void jsonParseToBSQ_APIResultConcept(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_array() && j.size() == 2, "JSON -> BSQ", 0, nullptr, "Expected JSON envelope for APIResult");
        bsq_validate(j[0].is_string(), "JSON -> BSQ", 0, nullptr, "Expected typename as key in envelope for APIResult");

        std::string tstr = j[0].get<std::string>();
        std::optional<const TypeInfo*> ofinfo_opt = TypeInfo::tryGetTypeInfoForKey(tstr);
        bsq_validate(ofinfo_opt.has_value(), "JSON -> BSQ", 0, nullptr, "Expected valid type for APIResult");

        const TypeInfo* ofinfo = ofinfo_opt.value();
        bsq_validate(ofinfo->supertypes != nullptr && std::find(ofinfo->supertypes, ofinfo->supertypes + ofinfo->supertypescount, tinfo->bsqtypeid) != ofinfo->supertypes + ofinfo->supertypescount, "JSON -> BSQ", 0, nullptr, "Expected supertype for APIResult");
        
        U val{};
        ofinfo->opdispatch.jsonParseToBSQFp(ofinfo, j[1], &val);
        
        *(BoxedUnion<U>*)resptr = BoxedUnion<U>(ofinfo, val);
    }

    template<ConceptUnionRepr U>
    void parseToBSQ_APIResultConcept(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::Identifier, "JSON -> BSQ", 0, nullptr, "Expected identifier token for APIResult");

        std::string tstr = lexer->getTokenIdentifierAsString();
        std::optional<const TypeInfo*> ofinfo_opt = TypeInfo::tryGetTypeInfoForKey(tstr);
        bsq_validate(ofinfo_opt.has_value(), "JSON -> BSQ", 0, nullptr, "Expected valid type for APIResult");

        const TypeInfo* ofinfo = ofinfo_opt.value();
        bsq_validate(ofinfo->supertypes != nullptr && std::find(ofinfo->supertypes, ofinfo->supertypes + ofinfo->supertypescount, tinfo->bsqtypeid) != ofinfo->supertypes + ofinfo->supertypescount, "JSON -> BSQ", 0, nullptr, "Expected supertype for APIResult");
        
        U val{};
        ofinfo->opdispatch.parseToBSQFp(ofinfo, lexer, &val);
        *(BoxedUnion<U>*)resptr = BoxedUnion<U>(ofinfo, val);
    }

    template<ConceptUnionRepr U>
    json bsqToJSON_APIResultConcept(const TypeInfo* tinfo, const void* valptr)
    {
        BoxedUnion<U> u = *(const BoxedUnion<U>*)valptr;

        json j = u.typeinfo->opdispatch.bsqToJSONFp(u.typeinfo, &u.data);
        return json::array({ u.typeinfo->typekey, j });
    }

    template<ConceptUnionRepr U>
    void bsqToBAPI_APIResultConcept(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        BoxedUnion<U> u = *(const BoxedUnion<U>*)valptr;
        u.typeinfo->opdispatch.bsqToBAPIFp(u.typeinfo, &u.data, builder);
    }

    template<ConceptUnionRepr U>
    void displayValue_APIResultConcept(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        BoxedUnion<U> u = *(const BoxedUnion<U>*)valptr;
        u.typeinfo->opdispatch.displayFp(u.typeinfo, &u.data, os, indent);
    }
}
