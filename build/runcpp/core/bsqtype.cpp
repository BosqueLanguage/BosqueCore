#include "bsqtype.h"

namespace ᐸRuntimeᐳ
{
    ////////////////////////////////
    //Standard processing functions for Enum types
    ////////////////////////////////

    void jsonParseToBSQ_Enum(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_string(), "JSON -> BSQ", 0, nullptr, "Expected string for enum type");

        std::string sstr = j.get<std::string>();
        size_t hashpos = sstr.find('#');
        bsq_validate(hashpos != std::string::npos, "JSON -> BSQ", 0, nullptr, "Expected '#' in enum string");
        std::string typekey = sstr.substr(0, hashpos);
        std::string member = sstr.substr(hashpos + 1);

        bsq_validate(typekey == tinfo->typekey, "JSON -> BSQ", 0, nullptr, "Enum type key mismatch");

        std::pair<size_t, const char**> members = TypeInfo::enuminfomap.at(tinfo->bsqtypeid);
        auto eiter = std::find_if(members.second, members.second + members.first, [member](const char* ev) { return member == ev; });

        bsq_validate(eiter != members.second + members.first, "JSON -> BSQ", 0, nullptr, "Expected valid enum member");
        uint64_t idx = (uint64_t)std::distance(members.second, eiter);

        void* args[1] = { &idx };
        tinfo->opdispatch.validatingConstructorFp(args, resptr);
    }

    void parseToBSQ_Enum(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected identifier for enum type");
        lexer->consume();

        bsq_validate(lexer->getCurrentTokenType() == BAPITokenType::LiteralSymbol && lexer->testIsSymbol('#'), "BAPI -> BSQ", 0, nullptr, "Expected '#' symbol for enum type");
        lexer->consume();

        std::pair<size_t, const char**> members = TypeInfo::enuminfomap.at(tinfo->bsqtypeid);
        auto eiter = std::find_if(members.second, members.second + members.first, [lexer](const char* ev) { return lexer->testDataMatchesID(ev); });
    
        bsq_validate(eiter != members.second + members.first, "BAPI -> BSQ", 0, nullptr, "Expected valid enum member");
        uint64_t idx = (uint64_t)std::distance(members.second, eiter);
        
        void* args[1] = { &idx };
        tinfo->opdispatch.validatingConstructorFp(args, resptr);
    }

    json bsqToJSON_Enum(const TypeInfo* tinfo, const void* valptr)
    {
        uint64_t vv = *(const uint64_t*)valptr;
        std::pair<size_t, const char**> members = TypeInfo::enuminfomap.at(tinfo->bsqtypeid);

        return json(std::string(tinfo->typekey) + '#' + members.second[vv]);
    }
    
    void bsqToBAPI_Enum(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        uint64_t vv = *(const uint64_t*)valptr;
        std::pair<size_t, const char**> members = TypeInfo::enuminfomap.at(tinfo->bsqtypeid);

        builder->appendConstString(tinfo->typekey);
        builder->appendChar('#');
        builder->appendConstString(members.second[vv]);
    }

    void displayValue_Enum(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        uint64_t vv = *(const uint64_t*)valptr;
        std::pair<size_t, const char**> members = TypeInfo::enuminfomap.at(tinfo->bsqtypeid);

        os << getDisplayIndent(indent) << tinfo->typekey << '#' << members.second[vv];
    }

    ////////////////////////////////
    //Standard processing functions for Typedecl types
    ////////////////////////////////
    void jsonParseToBSQ_Typedecl(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        void* val = alloca(ofinfo->bytesize);
        ofinfo->opdispatch.jsonParseToBSQFp(ofinfo, j, val);

        tinfo->opdispatch.validatingConstructorFp(&val, resptr);
    }

    void parseToBSQ_Typedecl(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        void* val = alloca(ofinfo->bytesize);
        ofinfo->opdispatch.parseToBSQFp(ofinfo, lexer, val);

        tinfo->opdispatch.validatingConstructorFp(&val, resptr);

        if(lexer->testIsSymbol('<')) {
            lexer->consume();
    
            bsq_validate(lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected type for typedecl");
            lexer->consume();
            bsq_validate(lexer->testIsSymbol('>'), "BAPI -> BSQ", 0, nullptr, "Expected symbol '>'");
            lexer->consume();
        }
    }

    json bsqToJSON_Typedecl(const TypeInfo* tinfo, const void* valptr)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        return ofinfo->opdispatch.bsqToJSONFp(ofinfo, valptr);
    }

    void bsqToBAPI_Typedecl(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);
        ofinfo->opdispatch.bsqToBAPIFp(ofinfo, valptr, builder);

        builder->appendChar('<');
        builder->appendConstString(tinfo->typekey);
        builder->appendChar('>');
    }

    void displayValue_Typedecl(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[0].fieldbsqtypeid);

        os << getDisplayIndent(indent);
        ofinfo->opdispatch.displayFp(ofinfo, valptr, os, indent);
        os << '<' << tinfo->typekey << '>';
    }

    ////////////////////////////////
    //Standard processing functions for Entity types
    ////////////////////////////////
    const void* accessEntityMemberFieldPtr(const TypeInfo* tinfo, const void* valptr, size_t idx) 
    {
        if(tinfo->tag != LayoutTag::Ref) {
            //not a pointer, just load the slot index as T
            return valptr + idx;
        }
        else {
            assert(tinfo->tag == LayoutTag::Ref);

            //dereference pointer in cell and then get the slot at index
            const void* ptrslots = *((const void**)valptr);
            return ptrslots + idx;
        }
    }

    void jsonParseToBSQ_Entity(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_object(), "BAPI -> BSQ", 0, nullptr, "Expected JSON object for entity");

        void* valdata = alloca(tinfo->bytesize);
        void** valptrs = (void**)alloca(tinfo->slotcount * sizeof(void*));
        std::fill(valptrs, valptrs + tinfo->slotcount, nullptr);

        void* cslot = valdata;
        for(size_t i = 0; i < tinfo->ftablecount; ++i)
        {
            const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[i].fieldbsqtypeid);
            std::string fieldname = tinfo->ftable[i].fname;

            if(j.contains(fieldname)) {
                ofinfo->opdispatch.jsonParseToBSQFp(ofinfo, j[fieldname], cslot);
                valptrs[i] = cslot;
            }

            cslot += ofinfo->slotcount;
        }

        tinfo->opdispatch.validatingConstructorFp(valptrs, resptr);
    }

    void parseToBSQ_Entity(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        bsq_validate(lexer->testIsType(tinfo->typekey), "BAPI -> BSQ", 0, nullptr, "Expected type for entity");
        lexer->consume();
        bsq_validate(lexer->testIsSymbol('{'), "BAPI -> BSQ", 0, nullptr, "Expected { for entity");
        lexer->consume();

        void* valdata = alloca(tinfo->bytesize);
        void** valptrs = (void**)alloca(tinfo->slotcount * sizeof(void*));
        std::fill(valptrs, valptrs + tinfo->slotcount, nullptr);

        bool first = true;
        size_t cpos = 0;
        while(!lexer->testIsSymbol('}')) {
            if(first) {
                first = false;
            }
            else {
                bsq_validate(lexer->testIsSymbol(','), "BAPI -> BSQ", 0, nullptr, "Expected ',' between args for entity");
                lexer->consume();
            }

            if(!lexer->constructorEqualsPeek()) {
                auto finfo = std::find_if(tinfo->ftable, tinfo->ftable + tinfo->ftablecount, [&lexer](const TypeLayoutInfo& fi) {
                    return lexer->testDataMatchesID(fi.fname);
                });
                bsq_validate(finfo != tinfo->ftable + tinfo->ftablecount, "BAPI -> BSQ", 0, nullptr, "Field name does not exist in entity");
                
                const TypeInfo* ftypeinfo = TypeInfo::getTypeInfoForID(finfo->fieldbsqtypeid);

                lexer->consume(); //eat Type
                lexer->consume(); //eat = symbol
                
                void* valpos = valdata + finfo->slotoffset;
                valptrs[std::distance(tinfo->ftable, finfo)] = valpos;
                parseToBSQ_Entity(ftypeinfo, lexer, (void*)valpos);

                cpos = std::numeric_limits<size_t>::max();
            }
            else {
                bsq_validate(cpos != std::numeric_limits<size_t>::max(), "BAPI -> BSQ", 0, nullptr, "Positional values must come before named arguments");
                bsq_validate(cpos < tinfo->ftablecount, "BAPI -> BSQ", 0, nullptr, "Too many (positional) values for constructor");

                const TypeLayoutInfo* finfo = tinfo->ftable + cpos;
                const TypeInfo* ftypeinfo = TypeInfo::getTypeInfoForID(finfo->fieldbsqtypeid);

                if(lexer->testDataMatches("_", 1)) {
                    //explict use of default
                    valptrs[cpos] = nullptr;    
                }
                else {
                    void* valpos = valdata + finfo->slotoffset;
                    valptrs[cpos] = valpos;
                    parseToBSQ_Entity(ftypeinfo, lexer, (void*)valpos);
                }

                cpos++;
            }
        }
        bsq_validate(lexer->testIsSymbol('}'), "BAPI -> BSQ", 0, nullptr, "Expected } for entity");
        lexer->consume();

        tinfo->opdispatch.validatingConstructorFp(valptrs, resptr);
    }

    json bsqToJSON_Entity(const TypeInfo* tinfo, const void* valptr)
    {
        json j = json::object();

        for(size_t i = 0; i < tinfo->ftablecount; ++i)
        {
            const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(tinfo->ftable[i].fieldbsqtypeid);
            std::string fieldname = tinfo->ftable[i].fname;

            const void* cslot = accessEntityMemberFieldPtr(tinfo, valptr, tinfo->ftable[i].slotoffset);
            j[fieldname] = ofinfo->opdispatch.bsqToJSONFp(ofinfo, cslot);
        }

        return j;
    }

    void bsqToBAPI_Entity(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        xxxx;
    }

    void displayValue_Entity(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        xxxx;
    }
}
