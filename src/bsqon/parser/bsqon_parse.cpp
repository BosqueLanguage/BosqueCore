#include "bsqon_parse.h"

#include <inttypes.h>

namespace BSQON
{
    std::vector<std::string> s_coreTypes = {
        "None", "Bool", "Int", "Nat", "BigInt", "BigNat", "Rational", "Float", "Decimal", "String", "ASCIIString",
        "ByteBuffer", "DateTime", "UTCDateTime", "PlainDate", "PlainTime", "TickTime", "LogicalTime", "ISOTimeStamp", U"UUIDv4", U"UUIDv7", U"SHAContentHash", 
        "LatLongCoordinate", "Regex", "Nothing"
    };

    bool s_dayInMonth(uint8_t d, uint8_t m, uint16_t y)
    {
        if(m == 1) {
            if(s_isLeapYear(y)) {
                return d <= 29;
            }
            else {
                return d <= 28;
            }
        }
        else {
            if(m == 3 || m == 5 || m == 8 || m == 10) {
                return d <= 30;
            }
            else {
                return d <= 31;
            }
        }
    }

    bool s_isLeapYear(uint16_t y)
    {
        if(y == 1900 || y == 2100 || y == 2200) {
            return false;
        }
        else {
            return y % 4 == 0;
        }
    }

    bool Parser::isValidNat(const std::string nv, int64_t& vv)
    {
        auto ecount = sscanf(nv.c_str(), "%" SCNd64, vv);
        return ecount == 1 && 0 <= vv && vv <= Type::MAX_SAFE_NUMBER; 
    }

    bool Parser::isValidInt(const std::string nv, int64_t& vv)
    {
        auto ecount = sscanf(nv.c_str(), "%" SCNd64, vv);
        return ecount == 1 && Type::MIN_SAFE_NUMBER <= vv && vv <= Type::MAX_SAFE_NUMBER;
    }

    bool Parser::isValidWCTime(const std::string nv, uint64_t& vv)
    {
        auto ecount = sscanf(nv.c_str(), "%" SCNu64, vv);
        return ecount == 1;
    }

    bool Parser::processDateInfo(const std::string& ds, uint16_t& yy, uint8_t& mm, uint8_t& dd)
    {
        auto pp = sscanf(ds.c_str(), "%4" SCNu16 "-%2" SCNu8 "-%2" SCNu8, yy, mm, dd);

        return pp == 3 && (1900 <= yy && yy <= 2200) && mm < 12 && s_dayInMonth(dd, mm, yy);
    }

    bool Parser::processTimeInfo(const std::string& ds, uint8_t& hh, uint8_t& mm, uint8_t& ss)
    {
        auto pp = sscanf(ds.c_str(), "%2" SCNu8 ":%2" SCNu8 ":%2" SCNu8, hh, mm, ss);

        return pp == 3 && hh < 24 && mm < 60 && ss < 61;
    }

    bool Parser::processMillisInfo(const std::string& ds, uint16_t& millis)
    {
        auto pp = sscanf(ds.c_str(), ".%3" SCNu16, millis);

        return pp == 1 && millis < 1000;
    }

    bool Parser::processTZInfo(const std::string& ds, const char** tz)
    {
        std::string ttz;
        if(ds.starts_with("{")) {
            ttz = ds.substr(1, ds.size() - 2); //trim {...}
        }
        else {
            ttz = ds;
        }

        auto tzii = this->tzset.insert(ttz);
        *tz = tzii.first->c_str();
        
        return true;
    }

    std::vector<std::pair<std::string, Value*>> Parser::processPropertiesForRecord(const RecordType* ttype, BSQON_AST_BraceValueNode* node)
    {
        xxxx;
    }

    std::vector<Value*> Parser::processPropertiesForEntity(const StdEntityType* ttype, BSQON_AST_BraceValueNode* node)
    {
        xxxx;
    }

    std::vector<Value*> Parser::processPropertiesForSequence(const Type* etype, BSQON_AST_BracketValueNode* node)
    {
        xxxx;
    }
        
    std::vector<Value*> Parser::processPropertiesForMap(const Type* keytype, const Type* valtype, BSQON_AST_BraceValueNode* node)
    {
        xxxx;
    }

    ////////////////////////////////////////////////////////////////////////////////

    const Type* Parser::resolveTypeFromNameList(std::string basenominal, std::vector<const Type*> terms)
    {
        std::string baseprefix = basenominal.substr(0, basenominal.find("::"));

        std::string scopedname;
        UnicodeString ubasename = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.from_bytes(basenominal);
        if (this->assembly->namespaces.at("Core")->hasTypenameDecl(ubasename)) {
            scopedname = basenominal;
        }
        else if (this->importmap.find(baseprefix) != this->importmap.end()) {
            scopedname = this->importmap.at(baseprefix) + basenominal.substr(baseprefix.size());
        }
        else {
            if (this->assembly->namespaces.find(baseprefix) != this->assembly->namespaces.end()) {
                scopedname = basenominal;
            }
            else {
                scopedname = this->defaultns + "::" + basenominal;
            }
        }

        if (!terms.empty()) {
            scopedname = scopedname + "<" + std::accumulate(terms.begin(), terms.end(), std::string(), [](std::string& a, Type* b) { return a + ", " + b->tkey; }) + ">";
        }

        auto titer = this->assembly->typerefs.find(scopedname);
        if (titer != this->assembly->typerefs.end()) {
            return titer->second;
        }
        else {
            auto aiter = this->assembly->aliasmap.find(scopedname);
            if(aiter != this->assembly->aliasmap.end()) {
                return aiter->second;
            }
            else {
                return UnresolvedType::singleton;
            }
        }
    }

    const Type* Parser::resolveAndCheckType(TypeKey tkey, SourcePos spos)
    {
        auto tt = this->assembly->resolveType(tkey);
        if(tt->isUnresolved()) {
            this->addError("Could not resolve type " + tkey, spos);
        }
            
        return tt;
    }

    const Type* Parser::processCoreType(std::string tname) 
    {
        return this->resolveTypeFromNameList(tname, {});
    }

    bool Parser::parseTemplateTermList(BSQON_TYPE_AST_List* tlist, std::vector<const Type*>& terms) 
    {
        for(auto curr = tlist; curr != NULL; curr = curr->next) {
            terms.push_back(this->parseType(curr->value));
        }
     
        return std::find_if(terms.begin(), terms.end(), [](Type* tt) { return tt->isUnresolved(); }) == terms.end();
    }

    const Type* Parser::parseTemplateTermList_One(SourcePos spos, BSQON_TYPE_AST_List* tlist) 
    {
        std::vector<const Type*> terms;
        bool ok = this->parseTemplateTermList(tlist, terms);

        if(ok && terms.size() == 1) {
            terms[0];
        }
        else {
            if(terms.size() != 1) {
                this->addError("Expected 1 template arg but got " + std::to_string(terms.size()), spos);
            }
            return UnresolvedType::singleton;
        }
    }

    std::pair<const Type*, const Type*> Parser::parseTemplateTermList_Two(SourcePos spos, BSQON_TYPE_AST_List* tlist) 
    {
        std::vector<const Type*> terms;
        bool ok = this->parseTemplateTermList(tlist, terms);

        if(ok && terms.size() == 2) {
            std::make_pair(terms[0], terms[1]);
        }
        else {
            if(terms.size() != 2) {
                this->addError("Expected 2 template arg but got " + std::to_string(terms.size()), spos);
            }
            return std::make_pair(UnresolvedType::singleton, UnresolvedType::singleton);
        }
    }

    const Type* Parser::parseTemplateTypeHelper_One(std::string sname, SourcePos spos, BSQON_TYPE_AST_List* tlist)
    {
        const Type* oftype = this->parseTemplateTermList_One(spos, tlist);
            
        if(oftype->isUnresolved()) {
            return UnresolvedType::singleton;
        } 
        else {
            return this->resolveAndCheckType(sname + "<" + oftype->tkey + ">", spos);
        }
    }

    const Type* Parser::parseTemplateTypeHelper_Two(std::string sname, SourcePos spos, BSQON_TYPE_AST_List* tlist)
    {
        std::pair<const Type*, const Type*> oftype = this->parseTemplateTermList_Two(spos, tlist);
            
        if(oftype.first->isUnresolved() || oftype.second->isUnresolved()) {
            return UnresolvedType::singleton;
        } 
        else {
            return this->resolveAndCheckType(sname + "<" + oftype.first->tkey + ", " + oftype.second->tkey + ">", spos);
        }
    }

    const Type* Parser::parseTemplateTypeHelper_OkErr(const Type* tresult, std::string sname, SourcePos spos)
    {
        if(tresult->isUnresolved()) {
            return UnresolvedType::singleton;
        } 
        else {
            return this->resolveAndCheckType(tresult->tkey + "::" + sname , spos);
        }
    }

    const Type* Parser::parseNominalType(BSQON_TYPE_AST_NominalNode* node)
    {
        std::string tname(node->name);

        bool iscore = std::find(s_coreTypes.begin(), s_coreTypes.end(), tname) != s_coreTypes.end();
        if (iscore) {
            return this->processCoreType(tname);
        }
        else if (tname == "StringOf") {
            return this->parseStringOfType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "ASCIIStringOf") {
            return this->parseASCIIStringOfType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Something") {
            return this->parseSomethingType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Option") {
            return this->parseOptionType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Result") {
            return this->parseResultType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Path") {
            return this->parsePathType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "PathFragment") {
            return this->parsePathFragmentType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "PathGlob") {
            return this->parsePathGlobType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "List") {
            return this->parseListType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Stack") {
            return this->parseStackType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Queue") {
            return this->parseQueueType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Set") {
            return this->parseSetType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "MapEntry") {
            return this->parseMapEntryType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else if (tname == "Set") {
            return this->parseMapType(Parser::convertSrcPos(node->base.pos), node->terms);
        }
        else {
            std::vector<const Type*> terms;
            this->parseTemplateTermList(node->terms, terms);
                
            if(std::any_of(terms.begin(), terms.end(), [](Type* tt) { return tt->isUnresolved(); })) {
                return UnresolvedType::singleton;
            }
            else {
                return this->resolveTypeFromNameList(tname, terms);
            }
        }
    }

    const Type* Parser::parseNominalTemplateType(BSQON_TYPE_AST_NominalExtNode* node)
    {
        const Type* roottype = this->parseNominalType(node->root);
        if(!roottype->tkey.starts_with("Result<")) {
            this->addError("Expected Result type", Parser::convertSrcPos(node->root->base.pos));
            return UnresolvedType::singleton;
        }
        
        std::string etype = std::string(node->ext);
        if(etype == "Ok") {
            return this->parseTemplateTypeHelper_OkErr(roottype, "Ok", Parser::convertSrcPos(node->base.pos));
        }
        else if(etype == "Err") {
            return this->parseTemplateTypeHelper_OkErr(roottype, "Err", Parser::convertSrcPos(node->base.pos));
        }
        else {
            this->addError("Expected Result::Ok or Result::Err type", Parser::convertSrcPos(node->root->base.pos));
            return UnresolvedType::singleton;
        }
    }

    const Type* Parser::parseTupleType(BSQON_TYPE_AST_TupleNode* node)
    {
        std::vector<const Type*> types;
        this->parseTemplateTermList(node->types, types);
                
        if(std::any_of(types.begin(), types.end(), [](Type* tt) { return tt->isUnresolved(); })) {
            return UnresolvedType::singleton;
        }
        else {
            std::vector<TypeKey> kk;
            std::transform(types.cbegin(), types.cend(), std::back_inserter(kk), [](const Type* tt){ return tt->tkey; });

            return new TupleType(kk);
        }
    }

        Type* parseRecordType() 
        {
            /*
        let entries: {pname: string, rtype: $TypeInfo.BSQType}[] = [];
        this.popToken();
        if(this.testToken(TokenKind.TOKEN_RBRACE)) {
            return this.lookupMustDefType("{}");
        }
        else {
            let first = true;
            while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                if(first) {
                    first = false;
                }
                else {
                    this.popToken();
                }
                
                const pname = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;
                const rtype = this.parseType();
                entries.push({ pname: pname, rtype: rtype });
            }
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

            const ees = entries.sort((a, b) => ((a.pname !== b.pname) ? (a.pname < b.pname ? -1 : 1) : 0)).map((ee) => `${ee.pname}: ${ee.rtype.tkey}`);
            return this.lookupMustDefType(`{${ees.join(", ")}}`);
        }
        */
        }

        Type* parseConceptSetType(Type* rtype, FollowSet syncTokens) 
        {
            std::vector<Type*> opts = {rtype};
            while (this->m_lex.testAndConsumeToken(TokenKind::TOKEN_AMP)) {
                opts.push_back(this->parseBaseType(syncTokens));
            }

            xxxx;
                return this.lookupMustDefType(opts.map((tt) => tt.tkey).sort((a, b) => ((a !== b) ? (a < b ? -1 : 1) : 0)).join("&"));
        }

        Type* parseBaseType(FollowSet syncTokens, TokenKind openParen, TokenKind closeParen)
        {
            Type* rtype = UnresolvedType::singleton;
            if (this->m_lex.testToken(TokenKind::TOKEN_TYPE)) {
                rtype = this->parseNominalType();
            }
            else if (this->m_lex.testToken(TokenKind::TOKEN_LBRACKET)) {
                rtype = this->parseTupleType();
            }
            else if (this->m_lex.testToken(TokenKind::TOKEN_LBRACE)) {
                rtype = this->parseRecordType();
            }
            else if(this->m_lex.testAndConsumeToken(TokenKind::TOKEN_LPAREN)) {
                rtype = this->parseType({TokenKind::TOKEN_RPAREN});

                if(!this->m_lex.testAndConsumeToken(TokenKind::TOKEN_RPAREN)) {
                    this->recoverErrorInsertExpected(U")", this->m_lex.peekToken());
                }
            }
            else {
                this->recoverErrorSynchronizeToken(U"Type", this->m_lex.peekToken(), syncTokens);
            }

            if(this->m_lex.testAndConsumeToken(TokenKind::TOKEN_AMP)) {
                return this->parseConceptSetType(rtype, syncTokens);
            }
            else {
                return rtype;
            }
        }

        Type* parseUnionType(FollowSet syncTokens, TokenKind openParen, TokenKind closeParen)
        {
            Type* lt = this->parseBaseType(syncTokens, openParen, closeParen);
            if (!this->m_lex.testToken(TokenKind::TOKEN_BAR)) {
                return lt;
            }
            else {
                std::vector<Type*> opts = {lt};
                while (this->m_lex.testAndConsumeToken(TokenKind::TOKEN_BAR)) {
                    opts.push_back(this->parseBaseType(syncTokens));
                }

                return this.lookupMustDefType(opts.map((tt) => tt.tkey).sort((a, b) => ((a !== b) ? (a < b ? -1 : 1) : 0)).join(" | "));
            }
        }

        Type* parseType(FollowSet syncTokens, TokenKind openParen, TokenKind closeParen)
        {
            return this->parseUnionType(syncTokens, openParen, closeParen);
        }

        Type* ParseRootType()
        {
            if (this->m_parse_bsqon) {
                return this->parseType({}, TokenKind::TOKEN_CLEAR, TokenKind::TOKEN_CLEAR);
            }
            else {
                this.raiseErrorIf(this.testToken(TokenKind.TOKEN_STRING), `Expected type: but got ${this.peekToken()?.value ?? "EOF"}`);
                this->m_lex.m_cpos++; //eat the "
                Type* tt = parseType({}, TokenKind::TOKEN_CLEAR, TokenKind::TOKEN_CLEAR);
                this->m_lex.m_cpos++; //eat the "

                return tt;
            }
        }


    ////////////////////////////////////////////////////////////////////////////////

    Type* Parser::parseType(BSQON_TYPE_AST_Node* node)
    {
        xxxx;
    }

    Value* Parser::parseNone(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_None) {
            this->addError("Expected None value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new NoneValue(t, Parser::convertSrcPos(node->pos));
    }
    
    Value* Parser::parseNothing(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Nothing) {
            this->addError("Expected Nothing value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new NothingValue(t, Parser::convertSrcPos(node->pos));
    }

    Value* Parser::parseBool(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_True && node->tag != BSQON_AST_TAG_False) {
            this->addError("Expected Boolean value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new BoolValue(t, Parser::convertSrcPos(node->pos), node->tag == BSQON_AST_TAG_True);
    }

    Value* Parser::parseNat(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Nat) {
            this->addError("Expected Nat value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        int64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'n'

        if(!Parser::isValidNat(nv, vv)) {
            this->addError("Nat value outside of valid range", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new NatNumberValue(t, Parser::convertSrcPos(node->pos), std::make_optional((uint64_t)vv), nv);
    }

    Value* Parser::parseInt(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Int) {
            this->addError("Expected Int value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        int64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'i'

        if(!Parser::isValidInt(nv, vv)) {
            this->addError("Int value outside of valid range", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new IntNumberValue(t, Parser::convertSrcPos(node->pos), std::make_optional(vv), nv);
    }

    Value* Parser::parseBigNat(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BigNat) {
            this->addError("Expected BigNat value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        int64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'N'

        bool smallv = Parser::isValidNat(nv, vv);

        return new NatNumberValue(t, Parser::convertSrcPos(node->pos), smallv ? std::make_optional((uint64_t)vv) : std::nullopt, std::string(BSQON_AST_asLiteralStandardNode(node)->data));
    }

    Value* Parser::parseBigInt(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BigInt) {
            this->addError("Expected BigInt value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        int64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'I'

        bool smallv = Parser::isValidNat(nv, vv);

        return new IntNumberValue(t, Parser::convertSrcPos(node->pos), smallv ? std::make_optional(vv) : std::nullopt, std::string(BSQON_AST_asLiteralStandardNode(node)->data));
    }

    Value* Parser::parseRational(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Rational) {
            this->addError("Expected Rational value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'R'

        if(nv.find('/') == std::string::npos) {
            return new RationalNumberValue(t, Parser::convertSrcPos(node->pos), nv, 1);
        }
        else {
            auto numerator = nv.substr(0, nv.find('/'));
            auto denominator = nv.substr(nv.find('/') + 1);

            int64_t denomv;
            if(!Parser::isValidNat(denominator, denomv)) {
                this->addError("Rational numerator outside of valid range", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            return new RationalNumberValue(t, Parser::convertSrcPos(node->pos), numerator, (uint64_t)denomv);
        }
    }

    Value* Parser::parseFloat(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Float) {
            this->addError("Expected Float value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'f'

        return new FloatNumberValue(t, Parser::convertSrcPos(node->pos), nv);
    }

    Value* Parser::parseDecmial(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Decimal) {
            this->addError("Expected Decimal value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'd'

        return new FloatNumberValue(t, Parser::convertSrcPos(node->pos), nv);
    }

    Value* Parser::parseString(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_String) {
            this->addError("Expected String value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto bstr = BSQON_AST_asLiteralStringNode(node)->data;
        StringValue* svopt = StringValue::createFromParse(t, Parser::convertSrcPos(node->pos), bstr->bytes, bstr->len);

        if(svopt == nullptr) {
            this->addError("Invalid escape characters in string", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return svopt;
    }

    Value* Parser::parseASCIIString(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_ASCIIString) {
            this->addError("Expected ASCIIString value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto bstr = BSQON_AST_asLiteralStringNode(node)->data;
        ASCIIStringValue* svopt = ASCIIStringValue::createFromParse(t, Parser::convertSrcPos(node->pos), bstr->bytes, bstr->len);

        if(svopt == nullptr) {
            this->addError("Invalid escape characters in ascii-string", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return svopt;
    }

    Value* Parser::parseByteBuffer(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_ByteBuffer) {
            this->addError("Expected ByteBuffer value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto buf = BSQON_AST_asLiteralStandardNode(node)->data;
        ByteBufferValue* bvopt = ByteBufferValue::createFromParse(t, Parser::convertSrcPos(node->pos), buf);

        if(bvopt == nullptr) {
            this->addError("Truncated byte value in buffer", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return bvopt;
    }

    Value* Parser::parseUUIDv4(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_UUIDv4) {
            this->addError("Expected UUIDv4 value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto uuid = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        if(!uuid.starts_with("uuid4")) {
            this->addError("Invalid UUIDv4 value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new UUIDv4Value(t, Parser::convertSrcPos(node->pos), uuid.substr(6, uuid.size() - 7));
    }

    Value* Parser::parseUUIDv7(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_UUIDv7) {
            this->addError("Expected UUIDv7 value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto uuid = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        if(!uuid.starts_with("uuid7")) {
            this->addError("Invalid UUIDv7 value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new UUIDv7Value(t, Parser::convertSrcPos(node->pos), uuid.substr(6, uuid.size() - 7));
    }

    Value* Parser::parseSHAHashcode(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_SHAHashcode) {
            this->addError("Expected SHAContentHash value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto hash = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        return new SHAContentHashValue(t, Parser::convertSrcPos(node->pos), hash.substr(4, hash.size() - 5));
    }

    Value* Parser::parseDateTime(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_DateTime) {
            this->addError("Expected DateTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto dstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        auto tstr = dstr.substr(dstr.find('T') + 1);
        auto tzstr = dstr.substr(dstr.find('@'));

        uint16_t year;
        uint8_t month, day;
        uint8_t hour, minute, second;
        const char* tz;

        if(!Parser::processDateInfo(dstr, year, month, day) || !Parser::processTimeInfo(tstr, hour, minute, second) || !Parser::processTZInfo(tzstr, &tz)) {
            this->addError("Invalid component in DateTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        DateTime dv = {year, month, day, hour, minute, second, (char*)tz};
        return new DateTimeValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parseUTCDateTime(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_UTCDateTime) {
            this->addError("Expected UTCDateTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto dstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        auto tstr = dstr.substr(dstr.find('T') + 1);
        auto tzstr = dstr.substr(dstr.find('@'));

        uint16_t year;
        uint8_t month, day;
        uint8_t hour, minute, second;

        if(!Parser::processDateInfo(dstr, year, month, day) || !Parser::processTimeInfo(tstr, hour, minute, second)) {
            this->addError("Invalid component in UTCDateTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        UTCDateTime dv = {year, month, day, hour, minute, second};
        return new UTCDateTimeValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parsePlainDate(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_PlainDate) {
            this->addError("Expected PlainDate value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto dstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);

        uint16_t year;
        uint8_t month, day;

        if(!Parser::processDateInfo(dstr, year, month, day)) {
            this->addError("Invalid component in PlainDate value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        PlainDate dv = {year, month, day};
        return new PlainDateValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parsePlainTime(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_PlainTime) {
            this->addError("Expected PlainTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto tstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);

        uint8_t hour, minute, second;

        if(!Parser::processTimeInfo(tstr, hour, minute, second)) {
            this->addError("Invalid component in PlainTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        PlainTime dv = {hour, minute, second};
        return new PlainTimeValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parseTickTime(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_TickTime) {
            this->addError("Expected TickTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto tstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);

        uint64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 't'

        if(!Parser::isValidWCTime(nv, vv)) {
            this->addError("TickTime value outside of valid range", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new TickTimeValue(t, Parser::convertSrcPos(node->pos), vv);
    }

    Value* Parser::parseLogicalTime(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_LogicalTime) {
            this->addError("Expected LogicalTime value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        uint64_t vv;
        std::string nv = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        nv.pop_back(); //remove the trailing 'l'

        if(!Parser::isValidWCTime(nv, vv)) {
            this->addError("LogicalTime value outside of valid range", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new LogicalTimeValue(t, Parser::convertSrcPos(node->pos), vv);
    }

    Value* Parser::parseISOTimeStamp(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Timestamp) {
            this->addError("Expected ISOTimeStamp value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto dstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        auto tstr = dstr.substr(dstr.find('T') + 1);
        
        uint16_t year;
        uint8_t month, day;
        uint8_t hour, minute, second;
        uint16_t millis;
        
        if(!Parser::processDateInfo(dstr, year, month, day) || !Parser::processTimeInfo(tstr, hour, minute, second) || !Parser::processMillisInfo(tstr, millis)) {
            this->addError("Invalid component in ISOTimeStamp value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        ISOTimeStamp dv = {year, month, day, hour, minute, second, millis};
        return new ISOTimeStampValue(t, Parser::convertSrcPos(node->pos), dv);
    }

    Value* Parser::parseRegex(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_Regex) {
            this->addError("Expected Regex value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto rstr = std::string(BSQON_AST_asLiteralStandardNode(node)->data);
        auto rri = this->assembly->regexliterals.find(rstr);

        if(rri == this->assembly->regexliterals.end()) {
            this->addError("Invalid Regex value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new RegexValue(t, Parser::convertSrcPos(node->pos), rri->second);
    }

    Value* Parser::parseLatLongCoordinate(const Type* t, struct BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_BraceValue && node->tag != BSQON_AST_TAG_TypedValue) {
            this->addError("Expected LatLongCoordinate value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        if(node->tag == BSQON_AST_TAG_TypedValue) {
            auto tnode = BSQON_AST_asTypedValueNode(node);
            const Type* ttype = this->parseType(tnode->type);
            if(ttype == nullptr || ttype->tkey != "LatLongCoordinate") {
                this->addError("Expected LatLongCoordinate value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            if(tnode->value->tag != BSQON_AST_TAG_BraceValue) {
                this->addError("Expected LatLongCoordinate value", Parser::convertSrcPos(node->pos));
                return new ErrorValue(t, Parser::convertSrcPos(node->pos));
            }

            node = tnode->value;
        }

        xxxx;
        auto data = this->processPropertiesForEntity(); BSQON_AST_asBraceValueNode(node);
        if(data->entries.)
        auto lli = this->assembly->latlongliterals.find(llstr);

        if(lli == this->assembly->latlongliterals.end()) {
            this->addError("Invalid LatLongCoordinate value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        return new LatLongCoordinateValue(t, Parser::convertSrcPos(node->pos), lli->second);
    }

    Value* Parser::parseStringOf(const Type* t, BSQON_AST_Node* node)
    {
        if(node->tag != BSQON_AST_TAG_StringOf && node->tag != BSQON_AST_TAG_String) {
            this->addError("Expected StringOf value", Parser::convertSrcPos(node->pos));
            return new ErrorValue(t, Parser::convertSrcPos(node->pos));
        }

        auto sof = BSQON_AST_asStringOfNode(node);

    }

    Value* Parser::parseASCIIStringOf(const Type* t, BSQON_AST_Node* node)
    {
        xxxx;
    }
}
