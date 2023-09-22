#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"

#include "lexer.h"
#include "../info/type_info.h"

namespace BSQON
{
    class Parser
    {
    private:
        AssemblyInfo* m_assembly;
        Lexer m_lex;

        std::list<std::vector<TokenKind>> m_recoverStack;

        const bool m_parse_bsqon;
        const bool m_parse_suggest;
        std::vector<ParseError> m_errors;

        const std::string m_defaultns;
        std::map<std::string, std::string> m_importmap;

        void recoverErrorAssumeTokenFound(UnicodeString expected, const LexerToken& found);
        void Parser::recoverErrorConsumeUntil(UnicodeString expected, const LexerToken& found);

        Type* resolveTypeFromNameList(UnicodeString basenominal, std::vector<Type*> terms)
        {
            std::string asciibasename = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.to_bytes(basenominal);
            std::string baseprefix = asciibasename.substr(0, asciibasename.find("::"));

            std::string scopedname;
            if (this->m_assembly->namespaces.at("Core")->hasTypenameDecl(basenominal)) {
                scopedname = asciibasename;
            }
            else if (this->m_importmap.find(baseprefix) != this->m_importmap.end()) {
                scopedname = this->m_importmap.at(baseprefix) + asciibasename.substr(baseprefix.size());
            }
            else {
                if (this->m_assembly->namespaces.find(baseprefix) != this->m_assembly->namespaces.end()) {
                    scopedname = asciibasename;
                }
                else {
                    scopedname = this->m_defaultns + "::" + asciibasename;
                }
            }

            if (!terms.empty()) {
                scopedname = scopedname + "<" + std::accumulate(terms.begin(), terms.end(), std::string(), [](std::string& a, Type* b) { return a + ", " + b->tkey; }) + ">";
            }

            auto titer = this->m_assembly->typerefs.find(scopedname);
            if (titer != this->m_assembly->typerefs.end()) {
                return titer->second;
            }
            else {
                return this->m_assembly->aliasmap.at(scopedname);
            }
        }

        Type* processCoreType(UnicodeString tname) 
        {
            return this->resolveTypeFromNameList(tname, {});
        }

        std::optional<Type*> parseTemplateTerm() 
        {
            if(!this->m_lex.testToken(TokenKind::TOKEN_LANGLE)) {
                return std::nullopt;
            }

            this->m_lex.popToken();
            auto ttype = this->parseType();

            if(!this->m_lex.testAndConsumeToken(TokenKind::TOKEN_RANGLE)) {
                if(this->m_lex.testToken(TokenKind::TOKEN_COMMA)) {
                    //probably trying to do 2 args but we just expected one -- consume to matching ">" or up the bracket stack
                    xxxx;
                }
                else {
                    this->recoverErrorAssumeTokenFound(U">", this->m_lex.peekToken());
                }
            }

            return ttype;
        }

        std::optional<std::pair<Type*, Type*>> parseTemplateTermPair()
        {
            if(!this->m_lex.testToken(TokenKind::TOKEN_LANGLE)) {
                return std::nullopt;
            }

        this->m_lex.popToken();
        auto ttype1 = this.parseType();

        if(!this->m_lex.testAndConsumeToken(TokenKind::TOKEN_COMMA)) {
            if(this->m_lex.testToken(TokenKind::TOKEN_RANGLE)) {
                //probably trying to do 1 arg but we expected 2
                xxxx;
            }
            else {
                xxxx;
            }
        }

        auto ttype2 = this.parseType();

        this.expectTokenAndPop(TokenKind.TOKEN_RANGLE);
        if(!this->m_lex.testAndConsumeToken(TokenKind::TOKEN_RANGLE)) {
            if(this->m_lex.testToken(TokenKind::TOKEN_COMMA)) {
                //probably trying to do 3 args but we just expected one -- consume to matching ">" or up the bracket stack
                xxxx;
            }
            else {
                this->recoverErrorAssumeTokenFound(U">", this->m_lex.peekToken());
            }
        }

        xxxx;
        return std::make_optional(std::make_pair(ttype1, ttype2));
    }

    private parseStringOfType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "StringOf", `Not a StringOf type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorREType), `Type StringOf requires a validator type argument`);

        return this.lookupMustDefType(`StringOf<${(oftype as $TypeInfo.ValidatorREType).tkey}>`);
    }

    private parseASCIIStringOfType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "ASCIIStringOf", `Not a ASCIIStringOf type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorREType), `Type ASCIIStringOf requires a validator type argument`);

        return this.lookupMustDefType(`ASCIIStringOf<${(oftype as $TypeInfo.ValidatorREType).tkey}>`);
    }
/*
    private parseSomethingType(opt: $TypeInfo.SomethingType | $TypeInfo.OptionType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Something", `Not a Something type`);

        return this.parseSomethingTypeComplete(opt);
    }

    private parseSomethingTypeComplete(opt: $TypeInfo.SomethingType | $TypeInfo.OptionType | undefined): $TypeInfo.BSQType {
        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`Something<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Something requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Something<${opt!.oftype}>`);

            return t;
        }
    }

    private parseOptionType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Option", `Not a Option type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined, `Type Option requires a type argument`);

        return this.lookupMustDefType(`Option<${(oftype as $TypeInfo.BSQType).tkey}>`);
    }

    private parsePathType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Path", `Not a Path type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorPthType), `Type Path requires a validator type argument`);

        return this.lookupMustDefType(`Path<${(oftype as $TypeInfo.ValidatorPthType).tkey}>`);
    }

    private parsePathFragmentType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "PathFragement", `Not a PathFragment type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorPthType), `Type PathFragement requires a validator type argument`);

        return this.lookupMustDefType(`PathFragment<${(oftype as $TypeInfo.ValidatorPthType).tkey}>`);
    }

    private parsePathGlobType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "PathGlob", `Not a PathGlob type`);

        const oftype = this.parseTemplateTerm();
        this.raiseErrorIf(oftype === undefined || !(oftype instanceof $TypeInfo.ValidatorPthType), `Type PathGlob requires a validator type argument`);

        return this.lookupMustDefType(`PathGlob<${(oftype as $TypeInfo.ValidatorPthType).tkey}>`);
    }

    private parseListType(opt: $TypeInfo.ListType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "List", `Not a List type`);

        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`List<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type List requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`List<${opt!.oftype}>`);

            return t;
        }
    }

    private parseStackType(opt: $TypeInfo.StackType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Stack", `Not a Stack type`);

        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`Stack<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Stack requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Stack<${opt!.oftype}>`);

            return t;
        }
    }

    private parseQueueType(opt: $TypeInfo.QueueType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Queue", `Not a Queue type`);

        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`Queue<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Queue requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Queue<${opt!.oftype}>`);

            return t;
        }
    }

    private parseSetType(opt: $TypeInfo.SetType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Set", `Not a Set type`);

        const oftype = this.parseTemplateTerm();
        if(oftype !== undefined) {
            const t = this.lookupMustDefType(`Set<${oftype.tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Set requires one type argument *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Set<${opt!.oftype}>`);

            return t;
        }
    }

    private parseMapEntryType(): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "MapEntry", `Not a MapEntry type`);

        const kvtype = this.parseTemplateTermPair();
        this.raiseErrorIf(kvtype === undefined, `Type MapEntry requires two type arguments`);

        return this.lookupMustDefType(`MapEntry<${kvtype![0].tkey}, ${kvtype![1].tkey}>`);
    }

    private parseMapType(opt: $TypeInfo.MapType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Map", `Not a Map type`);

        const kvtype = this.parseTemplateTermPair();
        if(kvtype !== undefined) {
            const t = this.lookupMustDefType(`Map<${kvtype[0].tkey}, ${kvtype[1].tkey}>`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Map requires two type arguments *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Map<${opt!.ktype}, ${opt!.vtype}>`);

            return t;
        }
    }

    private parseOkType(opt: $TypeInfo.OkType | $TypeInfo.ResultType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Result", `Not a Result::Ok type`);

        const tts = this.parseTemplateTermPair();
        const okn = this.popToken()!.value;
        this.raiseErrorIf(okn !== "Ok", `Not a Result::Ok type`);

        return this.parseOkTypeComplete(tts, opt);
    }

    private parseOkTypeComplete(tts: [$TypeInfo.BSQType, $TypeInfo.BSQType] | undefined, opt: $TypeInfo.OkType | $TypeInfo.ResultType | undefined): $TypeInfo.BSQType {
       if(tts !== undefined) {
            const t = this.lookupMustDefType(`Result<${tts[0].tkey}, ${tts[1].tkey}>::Ok`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Result::Ok requires two type arguments *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Result<${opt!.ttype}, ${opt!.etype}>::Ok`);

            return t;
        }
    }

    private parseErrType(opt: $TypeInfo.ErrorType | $TypeInfo.ResultType | undefined): $TypeInfo.BSQType {
        const llt = this.popToken()!.value;
        this.raiseErrorIf(llt !== "Result", `Not a Result::Err type`);

        const tts = this.parseTemplateTermPair();
        const okn = this.popToken()!.value;
        this.raiseErrorIf(okn !== "Err", `Not a Result::Err type`);

        return this.parseErrTypeComplete(tts, opt);
    }

    private parseErrTypeComplete(tts: [$TypeInfo.BSQType, $TypeInfo.BSQType] | undefined, opt: $TypeInfo.ErrorType | $TypeInfo.ResultType | undefined): $TypeInfo.BSQType {
        if(tts !== undefined) {
            const t = this.lookupMustDefType(`Result<${tts[0].tkey}, ${tts[1].tkey}>::Err`);
            this.raiseErrorIf(opt !== undefined && !this.m_assembly.checkConcreteSubtype(t, opt), `Type ${t.tkey} is not a subtype of expected type`);

            return t;
        }
        else {
            this.raiseErrorIf(opt === undefined, `Type Result::Err requires two type arguments *OR* can be used in a inferable context`);
            const t = this.lookupMustDefType(`Result<${opt!.ttype}, ${opt!.etype}>::Err`);

            return t;
        }
    }

    private parseResultTypeComplete(tts: [$TypeInfo.BSQType, $TypeInfo.BSQType]): $TypeInfo.BSQType {
        return this.lookupMustDefType(`Result<${tts[0].tkey}, ${tts[1].tkey}>`);
    }

    private isNominalTypePrefix(): boolean {
        const ntok = this.peekToken();
        return ntok !== undefined && ntok.kind === TokenKind.TOKEN_TYPE;
    }

    private parseNominalType(): $TypeInfo.BSQType {
        const ntok = this.peekToken();
        this.raiseErrorIf(ntok === undefined || ntok.kind !== TokenKind.TOKEN_TYPE, `Expected nominal type name but found ${ntok?.value ?? "EOF"}`);

        const tname = ntok!.value;
        if (_s_core_types.includes(tname)) {
            return this.processCoreType(tname);
        }
        else if (tname === "StringOf") {
            return this.parseStringOfType();
        }
        else if (tname === "ASCIIStringOf") {
            return this.parseASCIIStringOfType();
        }
        else if (tname === "Something") {
            return this.parseSomethingType(undefined);
        }
        else if (tname === "Option") {
            return this.parseOptionType();
        }
        else if (tname === "Path") {
            return this.parsePathType();
        }
        else if (tname === "PathFragment") {
            return this.parsePathFragmentType();
        }
        else if (tname === "PathGlob") {
            return this.parsePathGlobType();
        }
        else if (tname === "List") {
            return this.parseListType(undefined);
        }
        else if (tname === "Stack") {
            return this.parseStackType(undefined);
        }
        else if (tname === "Queue") {
            return this.parseQueueType(undefined);
        }
        else if (tname === "Set") {
            return this.parseSetType(undefined);
        }
        else if (tname === "MapEntry") {
            return this.parseMapEntryType();
        }
        else if (tname === "Set") {
            return this.parseMapType(undefined);
        }
        else if (tname === "Result") {
            this.popToken();
            const tts = this.parseTemplateTermPair();

            if (!this.testToken(TokenKind.TOKEN_COLON_COLON)) {
                this.raiseErrorIf(tts === undefined, `Type Result requires two type arguments`);
                return this.parseResultTypeComplete(tts!);
            }
            else {
                this.expectTokenAndPop(TokenKind.TOKEN_COLON_COLON);
                const tname = this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value;
                this.raiseErrorIf(tname !== "Ok" && tname !== "Err", `Unknown type (expected Ok or Err)`);

                if(tname === "Ok") {
                    return this.parseOkTypeComplete(tts, undefined);
                }
                else {
                    return this.parseErrTypeComplete(tts, undefined);
                }
            }
        }
        else {
            this.popToken();
            let tnames = [tname];
            while (this.testTokens(TokenKind.TOKEN_COLON_COLON, TokenKind.TOKEN_TYPE)) {
                this.popToken();
                tnames.push(this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value);
            }

            let terms: $TypeInfo.BSQType[] = [];
            if (this.testToken(TokenKind.TOKEN_LANGLE)) {
                this.popToken();

                while (terms.length === 0 || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if (this.testToken(TokenKind.TOKEN_COMMA)) {
                        this.popToken();
                    }

                    terms.push(this.parseType());
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RANGLE);
            }

            const lltype = this.resolveTypeFromNameList(tnames, terms);
            this.raiseErrorIf(lltype === undefined, `Could not resolve nominal type ${tnames.join("::")}`);

            return lltype;
        }
    }

    private parseTupleType(): $TypeInfo.BSQType {
        let entries: $TypeInfo.BSQType[] = [];
        this.popToken();
        if(this.testToken(TokenKind.TOKEN_RBRACKET)) {
            return this.lookupMustDefType("[]");
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
                
                entries.push(this.parseType());
            }
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            return this.lookupMustDefType(`[${entries.map((ee) => ee.tkey).join(", ")}]`);
        }
    }

    private parseRecordType(): $TypeInfo.BSQType {
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
    }

    private parseBaseType(): $TypeInfo.BSQType {
        if (this.testToken(TokenKind.TOKEN_TYPE)) {
            return this.parseNominalType();
        }
        else if (this.testToken(TokenKind.TOKEN_LBRACKET)) {
            return this.parseTupleType();
        }
        else if (this.testToken(TokenKind.TOKEN_LBRACE)) {
            return this.parseRecordType();
        }
        else {
            this.raiseError(`Unexpected token when parsing type: ${this.peekToken()?.value ?? "EOF"}`);
            return $TypeInfo.UnresolvedType.singleton;
        }
    }

    private parseConceptSetType(): $TypeInfo.BSQType {
        const lt = this.parseBaseType();
        if (!this.testToken(TokenKind.TOKEN_AMP)) {
            return lt;
        }
        else {
            let opts = [lt];
            while (this.testToken(TokenKind.TOKEN_AMP)) {
                this.popToken();
                opts.push(this.parseConceptSetType());
            }

            return this.lookupMustDefType(opts.map((tt) => tt.tkey).sort((a, b) => ((a !== b) ? (a < b ? -1 : 1) : 0)).join("&"));
        }
    }

    private parseUnionType(): $TypeInfo.BSQType {
        const lt = this.parseConceptSetType();
        if (!this.testToken(TokenKind.TOKEN_BAR)) {
            return lt;
        }
        else {
            let opts = [lt];
            while (this.testToken(TokenKind.TOKEN_BAR)) {
                this.popToken();
                opts.push(this.parseUnionType());
            }

            return this.lookupMustDefType(opts.map((tt) => tt.tkey).sort((a, b) => ((a !== b) ? (a < b ? -1 : 1) : 0)).join(" | "));
        }
    }

    private parseType(): $TypeInfo.BSQType {
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return this.parseUnionType();
        }
        else {
            this.raiseErrorIf(this.testToken(TokenKind.TOKEN_STRING), `Expected type: but got ${this.peekToken()?.value ?? "EOF"}`);
            this.m_cpos++; //eat the "
            const tt = this.parseUnionType();
            this.m_cpos++; //eat the "

            return tt;
        }
    }

    private peekType(): $TypeInfo.BSQType {
        const opos = this.m_cpos;
        const olt = this.m_lastToken;

        const tt = this.parseType();

        this.m_lastToken = olt;
        this.m_cpos = opos;

        return tt;
    }
/*
    private parseSrc(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.expectTokenAndPop(TokenKind.TOKEN_SRC);

        this.raiseErrorIf(this.m_srcbind === undefined, "Invalid use of $SRC binding");
        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(this.m_srcbind![1], oftype), `Reference $src has type ${this.m_srcbind![1].tkey} which is not a subtype of ${oftype.tkey}`);
        const rr = oftype.isconcretetype ? this.m_srcbind![0] : new $Runtime.UnionValue(this.m_srcbind![1].tkey, this.m_srcbind![0]);

        return BSQONParseResultInfo.create(rr, this.m_srcbind![1], this.m_srcbind![2], whistory);
    }

    private parseReference(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        const ref = this.expectTokenAndPop(TokenKind.TOKEN_REFERENCE).value;

        this.raiseErrorIf(!this.m_refs.has(ref), `Reference ${ref} not found`);
        const rinfo = this.m_refs.get(ref);

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(rinfo![1], oftype), `Reference ${ref} has type ${rinfo![1].tkey} which is not a subtype of ${oftype.tkey}`);
        const rr = oftype.isconcretetype ? rinfo![0] : new $Runtime.UnionValue(rinfo![1].tkey, rinfo![0]);

        return BSQONParseResultInfo.create(rr, rinfo![1], rinfo![2], whistory);
    }

    private parseBaseExpression(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        if (this.testToken(TokenKind.TOKEN_SRC)) {
            return this.parseSrc(oftype, whistory);
        }
        else if (this.testToken(TokenKind.TOKEN_REFERENCE)) {
            return this.parseReference(oftype, whistory);
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_LPAREN);
            const re = this.parseExpression(oftype, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);

            return re;
        }
    }

    private parsePostfixOp(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        const bexp = this.parseBaseExpression(oftype, true);

        let vv = bexp;
        while (this.testToken(TokenKind.TOKEN_DOT_NAME) || this.testToken(TokenKind.TOKEN_DOT_IDX) || this.testToken(TokenKind.TOKEN_LBRACKET)) {
            let aval: any = undefined;
            let ptype: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;
            let ptree: any = undefined;

            const vval = BSQONParseResultInfo.getParseValue(vv, true);
            const vtype = BSQONParseResultInfo.getValueType(vv, true)
            if (this.testToken(TokenKind.TOKEN_DOT_NAME)) {
                const iname = this.popTokenSafe().value.slice(1);

                if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_RECORD) {
                    aval = vtype.isconcretetype ? vval[iname] : vval.value[iname];
                    ptype = BSQONParseResultInfo.getHistory(vv, true)[iname][0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true)[iname][1];
                }
                else if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_STD_ENTITY) {
                    aval = vtype.isconcretetype ? vval[iname] : vval.value[iname];
                    ptype = BSQONParseResultInfo.getHistory(vv, true)[iname][0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true)[iname][1];
                }
                else if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_SOMETHING) {
                    this.raiseErrorIf(iname !== "value", `Expected 'value' property access but got ${iname}`);

                    aval = vtype.isconcretetype ? vval : vval.value;
                    ptype = BSQONParseResultInfo.getHistory(vv, true)[0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true)[1];
                }
                else if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_MAP_ENTRY) {
                    this.raiseErrorIf(iname !== "key" && iname !== "value", `Expected 'key' or 'value' property access but got ${iname}`);

                    if (iname === "key") {
                        vtype.isconcretetype ? vval[0] : vval.value[0];
                        ptype = BSQONParseResultInfo.getHistory(vv, true).key[0];
                        ptree = BSQONParseResultInfo.getHistory(vv, true).key[1];
                    }
                    else if (iname === "value") {
                        vtype.isconcretetype ? vval[1] : vval.value[1];
                        ptype = BSQONParseResultInfo.getHistory(vv, true).value[0];
                        ptree = BSQONParseResultInfo.getHistory(vv, true).value[1];
                    }
                }
                else {
                    this.raiseError(`Invalid use of '.' operator -- ${vtype.tkey} is not a record, nominal, option/something, or map entry type`);
                }
            }
            else if (this.testToken(TokenKind.TOKEN_DOT_IDX)) {
                this.raiseErrorIf(vtype.tag !== $TypeInfo.BSQTypeTag.TYPE_TUPLE, `Invalid use of '[]' operator -- ${vtype.tkey} is not a tuple type`);

                const idx = Number.parseInt(this.expectTokenAndPop(TokenKind.TOKEN_DOT_IDX).value.slice(1));
                const tuprepr = vtype.isconcretetype ? vval : vval.value;

                this.raiseErrorIf(idx >= tuprepr.length, `Invalid use of '[]' operator -- index ${idx} is out of bounds for tuple type ${BSQONParseResultInfo.getValueType(vv, true).tkey}`);
                aval = tuprepr[idx];
                ptype = BSQONParseResultInfo.getHistory(vv, true)[idx][0];
                ptree = BSQONParseResultInfo.getHistory(vv, true)[idx][1];
            }
            else {
                if (vtype.tag === $TypeInfo.BSQTypeTag.TYPE_LIST) {
                    this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
                    const eexp = this.parseExpression(this.m_assembly.typerefs.get("Nat") as $TypeInfo.BSQType, false);
                    this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

                    const lrepr = (vtype.isconcretetype ? vval : vval.value) as IList<any>;
                    aval = lrepr.get(eexp);
                    ptype = BSQONParseResultInfo.getHistory(vv, true).get(eexp)[0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true).get(eexp)[1];
                }
                //OTHER TYPES HERE
                else {
                    this.raiseErrorIf(vtype.tag !== $TypeInfo.BSQTypeTag.TYPE_MAP, `Invalid use of '[]' operator -- ${vtype.tkey} is not a map type`);

                    this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
                    const eexp = this.parseExpression(this.lookupMustDefType((BSQONParseResultInfo.getValueType(vv, true) as $TypeInfo.MapType).ktype), false);
                    this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

                    const lrepr = (vtype.isconcretetype ? vval : vval.value) as IMap<any, any>;
                    aval = lrepr.get(eexp);
                    ptype = BSQONParseResultInfo.getHistory(vv, true).get(eexp)[0];
                    ptree = BSQONParseResultInfo.getHistory(vv, true).get(eexp)[1];
                }
            }

            vv = BSQONParseResultInfo.create(aval, ptype, ptree, true);
        }

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(BSQONParseResultInfo.getValueType(vv, true), oftype), `Expression has type ${BSQONParseResultInfo.getValueType(vv, true).tkey} which is not a subtype of ${oftype.tkey}`);
        const rr = oftype.isconcretetype ? BSQONParseResultInfo.getParseValue(vv, true) : new $Runtime.UnionValue(BSQONParseResultInfo.getParseValue(vv, true), BSQONParseResultInfo.getValueType(vv, true));

        return BSQONParseResultInfo.create(rr, BSQONParseResultInfo.getParseValue(vv, true), BSQONParseResultInfo.getHistory(vv, true), whistory);
    }

    private parseExpression(oftype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        return this.parsePostfixOp(oftype, whistory);
    }

    private parseNone(whistory: boolean): BSQONParseResult {
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            this.expectTokenAndPop(TokenKind.TOKEN_NONE);
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_NULL);
        }
        return BSQONParseResultInfo.create(null, this.lookupMustDefType("None"), undefined, whistory);
    }

    private parseNothing(whistory: boolean): BSQONParseResult {
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            this.expectTokenAndPop(TokenKind.TOKEN_NOTHING);
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_NULL);
        }
        return BSQONParseResultInfo.create(undefined, this.lookupMustDefType("Nothing"), undefined, whistory);
    }

    private parseBool(whistory: boolean): BSQONParseResult {
        const tk = this.popToken();
        this.raiseErrorIf(tk === undefined || (tk.kind !== TokenKind.TOKEN_TRUE && tk.kind !== TokenKind.TOKEN_FALSE), `Expected boolean value but got -- ${tk?.value ?? "EOF"}`);

        return BSQONParseResultInfo.create(tk!.kind === TokenKind.TOKEN_TRUE, this.lookupMustDefType("Bool"), undefined, whistory);
    }
    
    private parseNat(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_NAT).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_INT).value;
        }
    
        const bv = Number.parseInt(tkval);
        this.raiseErrorIf(Number.isNaN(bv) || !Number.isFinite(bv), `Expected finite Nat number but got -- ${tkval}`);
        this.raiseErrorIf(bv < 0, `Nat value is negative -- ${tkval}`);
        this.raiseErrorIf(bv > $Constants.FIXED_NUMBER_MAX, `Nat value is larger than max value -- ${tkval}`);
    
        return BSQONParseResultInfo.create(bv, this.lookupMustDefType("Nat"), undefined, whistory);
    }

    private parseInt(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_INT).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_INT).value;
        }
    
        const bv = Number.parseInt(tkval);
        this.raiseErrorIf(Number.isNaN(bv) || !Number.isFinite(bv), `Expected finite Int number but got -- ${tkval}`);
        this.raiseErrorIf(bv < $Constants.FIXED_NUMBER_MIN, `Int value is smaller than min value -- ${tkval}`);
        this.raiseErrorIf(bv > $Constants.FIXED_NUMBER_MAX, `Int value is larger than max value -- ${tkval}`);
        
        return BSQONParseResultInfo.create(bv, this.lookupMustDefType("Int"), undefined, whistory);
    }

    private parseBigNat(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_BIG_NAT).value.slice(0, -1);
        }
        else {
            const tk = this.popToken();
            this.raiseErrorIf(tk === undefined || (tk.kind !== TokenKind.TOKEN_INT && tk.kind !== TokenKind.TOKEN_STRING), `Expected BigNat but got ${tk?.value ?? "EOF"}`);
    
            if(tk!.kind === TokenKind.TOKEN_INT) {
                tkval = tk!.value;
            }
            else {
                tkval = tk!.value.slice(1, -1);
                this.raiseErrorIf(!_s_natCheckRe.test(tkval), `Expected BigInt: but got ${tkval}`);
            }
        }
    
        return BSQONParseResultInfo.create(BigInt(tkval), this.lookupMustDefType("BigNat"), undefined, whistory);
    }
    private parseBigInt(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_BIG_INT).value.slice(0, -1);
        }
        else {
            const tk = this.popToken();
            this.raiseErrorIf(tk === undefined || (tk.kind !== TokenKind.TOKEN_INT && tk.kind !== TokenKind.TOKEN_STRING), `Expected BigInt but got ${tk?.value ?? "EOF"}`);
    
            if(tk!.kind === TokenKind.TOKEN_INT) {
                tkval = tk!.value;
            }
            else {
                tkval = tk!.value.slice(1, -1);
                this.raiseErrorIf(!_s_intCheckRe.test(tkval), `Expected BigInt: but got ${tkval}`);
            }
        }
    
        return BSQONParseResultInfo.create(BigInt(tkval), this.lookupMustDefType("BigInt"), undefined, whistory);
    }

    private parseRational(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_RATIONAL).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_rationalCheckRe.test(tkval), `Expected float but got ${tkval}`);
        }
    
        return BSQONParseResultInfo.create(new Fraction(tkval), this.lookupMustDefType("Rational"), undefined, whistory);
    }

    private parseFloat(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_FLOAT).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_FLOAT).value;
            this.raiseErrorIf(!_s_floatCheckRe.test(tkval), `Expected float but got ${tkval}`);
        }
    
        return BSQONParseResultInfo.create(Number.parseFloat(tkval), this.lookupMustDefType("Float"), undefined, whistory);
    }

    private parseDecimal(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_DECIMAL).value.slice(0, -1);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_FLOAT).value;
            this.raiseErrorIf(!_s_floatCheckRe.test(tkval), `Expected decimal but got ${tkval}`);
        }
    
        return BSQONParseResultInfo.create(new Decimal(tkval), this.lookupMustDefType("Decimal"), undefined, whistory);
    }

    private parseString(whistory: boolean): BSQONParseResult {
        const tstr = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
        const rstr = this.unescapeString(tstr);

        return BSQONParseResultInfo.create(rstr, this.lookupMustDefType("String"), undefined, whistory);
    }

    private parseASCIIString(whistory: boolean): BSQONParseResult {
        let tkval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_ASCII_STRING).value.slice(7, -2);
        }
        else {
            tkval = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_asciiStringCheckRe.test(tkval), `Expected ASCII string but got ${tkval}`);
        }
    
        const rstr = this.unescapeString(tkval);
        return BSQONParseResultInfo.create(rstr, this.lookupMustDefType("ASCIIString"), undefined, whistory);
    }

    private parseByteBuffer(whistory: boolean): BSQONParseResult {
        let tbval: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tbval = this.expectTokenAndPop(TokenKind.TOKEN_BYTE_BUFFER).value.slice(3, -1);
        }
        else {
            tbval = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_bytebuffCheckRe.test(tbval), `Expected byte buffer but got ${tbval}`);
        }
    
        return BSQONParseResultInfo.create(tbval, this.lookupMustDefType("ByteBuffer"), undefined, whistory);
    }

    private parseDateTime(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQDateTime | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_DATE_TIME).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_fullTimeCheckRE.test(tk), `Expected date+time but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("DateTime"), undefined, whistory);
    }

    private parseUTCDateTime(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQDateTime | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_UTC_DATE_TIME).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_fullTimeUTCCheckRE.test(tk), `Expected UTC date+time but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("UTCDateTime"), undefined, whistory);
    }

    private parsePlainDate(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQDate | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_DATE).value;
            dd = generateDate(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_dateOnlyCheckRE.test(tk), `Expected plain date but got ${tk}`);
    
            dd = generateDate(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("PlainDate"), undefined, whistory);
    }

    private parsePlainTime(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQTime | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_TIME).value;
            dd = generateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_timeOnlyCheckRE.test(tk), `Expected plain time but got ${tk}`);
    
            dd = generateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("PlainTime"), undefined, whistory);
    }

    private parseTickTime(whistory: boolean): BSQONParseResult {
        let tt: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_TICK_TIME).value.slice(0, -1);
        }
        else {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_tickTimeCheckRE.test(tt), `Expected tick time but got ${tt}`);
        }
    
        return BSQONParseResultInfo.create(BigInt(tt), this.lookupMustDefType("TickTime"), undefined, whistory);
    }

    private parseLogicalTime(whistory: boolean): BSQONParseResult {
        let tt: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_LOGICAL_TIME).value.slice(0, -1);
        }
        else {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_logicalTimeCheckRE.test(tt), `Expected logical time but got ${tt}`);
        }
    
        return BSQONParseResultInfo.create(BigInt(tt), this.lookupMustDefType("LogicalTime"), undefined, whistory);
    }

    private parseISOTimeStamp(whistory: boolean): BSQONParseResult {
        let dd: $Runtime.BSQDateTime | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_TIMESTAMP).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_isoStampCheckRE.test(tk), `Expected timestamp but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);
        }
    
        return BSQONParseResultInfo.create(dd, this.lookupMustDefType("ISOTimeStamp"), undefined, whistory);
    }

    private parseUUIDv4(whistory: boolean): BSQONParseResult {
        let uuid: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_UUID).value;
            this.raiseErrorIf(!tk.startsWith("uuid4{"), `Expected UUIDv4 but got ${tk}`);
    
            uuid = tk.slice(6, -1);
        }
        else {
            uuid = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_uuidCheckRE.test(uuid), `Expected UUIDv4 but got ${uuid}`);
        }
    
        return BSQONParseResultInfo.create(uuid, this.lookupMustDefType("UUIDv4"), undefined, whistory);
    }

    private parseUUIDv7(whistory: boolean): BSQONParseResult {
        let uuid: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_UUID).value;
            this.raiseErrorIf(!tk.startsWith("uuid7{"), `Expected UUIDv7 but got ${tk}`);
    
            uuid = tk.slice(6, -1);
        }
        else {
            uuid = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_uuidCheckRE.test(uuid), `Expected UUIDv7 but got ${uuid}`);
        }
    
        return BSQONParseResultInfo.create(uuid, this.lookupMustDefType("UUIDv7"), undefined, whistory);
    }

    private parseSHAContentHash(whistory: boolean): BSQONParseResult {
        let sh: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            sh = this.expectTokenAndPop(TokenKind.TOKEN_SHA_HASH).value.slice(5, -1);
        }
        else {
            sh = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_shahashCheckRE.test(sh), `Expected SHA 512 hash but got ${sh}`);
        }
    
        return BSQONParseResultInfo.create(sh, this.lookupMustDefType("SHAContentHash"), undefined, whistory);
    }

    private parseRegex(whistory: boolean): BSQONParseResult {
        let re: string | undefined = undefined;
        if(this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            re = this.expectTokenAndPop(TokenKind.TOKEN_REGEX).value;
        }
        else {
            re = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            this.raiseErrorIf(!_s_regexCheckRe.test(re), `Expected a regex string but got ${re}`);
        }
    
        return BSQONParseResultInfo.create(re, this.lookupMustDefType("Regex"), undefined, whistory);
    }

    private parseLatLongCoordinate(whistory: boolean): BSQONParseResult {
        let llc: [number, number] | undefined = undefined;
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const ttype = this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value;
            this.raiseErrorIf(ttype !== "LatLongCoordinate", `Expected LatLongCoordinate but got ${ttype}`);
    
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
            const lat = this.parseFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const long = this.parseFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
    
            llc = [lat, long];
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const lat = this.parseFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const long = this.parseFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);
    
            llc = [lat, long];
        }

        this.raiseErrorIf(-90.0 <= llc[0] && llc[0] <= 90.0 && -180.0 < llc[1] && llc[1] <= 180.0, `LatLongCoordinate out of range: ${llc}`)
        return BSQONParseResultInfo.create(llc, this.lookupMustDefType("LatLongCoordinate"), undefined, whistory);
    }

    private parseStringOfWithType(whistory: boolean): [BSQONParseResult, $TypeInfo.BSQTypeKey] {
        const rawtk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
        const tk = this.unescapeString(rawtk);
        const st = this.parseNominalType() as $TypeInfo.ValidatorEntityType;

        const vre = this.m_assembly.revalidators.get(st.oftype);
        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), tk), `String literal does not satisfy the required format: ${st.oftype} (${vre})`);

        const stt = this.lookupMustDefType(`StringOf<${st.tkey}>`) as $TypeInfo.StringOfType;
        return [BSQONParseResultInfo.create(tk, stt, undefined, whistory), stt.tkey];
    }

    private parseStringOf(ttype: $TypeInfo.StringOfType, whistory: boolean): BSQONParseResult {
        let sval: string | undefined = undefined;
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);

            if(this.isNominalTypePrefix()) {
                const st = this.parseNominalType();
                this.raiseErrorIf(st.tkey !== ttype.oftype, `Expected ${ttype.oftype} but got StringOf<${st.tkey}>`);
            }

            sval = this.unescapeString(tk);
        }
        else {
            const rawtk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            sval = this.unescapeString(rawtk);
        }

        const vre = this.m_assembly.revalidators.get(ttype.oftype);
        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), sval), `String literal does not satisfy the required format: ${ttype.oftype} (${vre})`);

        return BSQONParseResultInfo.create(sval, ttype, undefined, whistory);
    }

    private parseASCIIStringOfWithType(whistory: boolean): [BSQONParseResult, $TypeInfo.BSQTypeKey] {
        const rawtk = this.expectTokenAndPop(TokenKind.TOKEN_ASCII_STRING).value.slice(7, -2);
        const tk = this.unescapeString(rawtk);
        const st = this.parseASCIIStringOfType() as $TypeInfo.ValidatorEntityType;

        const vre = this.m_assembly.revalidators.get(st.oftype);
        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), tk), `String literal does not satisfy the required format: ${st.oftype} (${vre})`);

        const stt = this.lookupMustDefType(`ASCIIStringOf<${st.tkey}>`) as $TypeInfo.ASCIIStringOfType;
        return [BSQONParseResultInfo.create(tk, stt, undefined, whistory), stt.tkey];
    }

    private parseASCIIStringOf(ttype: $TypeInfo.ASCIIStringOfType, whistory: boolean): BSQONParseResult {
        let sval: string | undefined = undefined;
        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ASCII_STRING).value;

            if (this.isNominalTypePrefix()) {
                const st = this.parseASCIIStringOfType();
                this.raiseErrorIf(st.tkey !== ttype.oftype, `Expected ${ttype.tag} but got ASCIIStringOf<${st.tkey}>`);
            }

            const rawtk = tk.slice(7, -2);
            sval = this.unescapeString(rawtk);
        }
        else {
            const rawtk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value.slice(1, -1);
            sval = this.unescapeString(rawtk);
        }

        const vre = this.m_assembly.revalidators.get(ttype.oftype);
        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), sval), `ASCIIString literal does not satisfy the required format: ${ttype.oftype} (${vre})`);

        return BSQONParseResultInfo.create(sval, ttype, undefined, whistory);
    }

    private parsePath(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.raiseError("NOT IMPLEMENTED: PATH");
    }

    private parsePathFragment(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.raiseError("NOT IMPLEMENTED: PATH FRAGMENT");
    }

    private parsePathGlob(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        this.raiseError("NOT IMPLEMENTED: PATH GLOB");
    }

    private parseSomething(ttype: $TypeInfo.SomethingType | $TypeInfo.OptionType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        let vv = undefined;
        let stype: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;

        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (this.testToken(TokenKind.TOKEN_SOMETHING)) {
                this.popToken();
                stype = this.parseSomethingTypeComplete(ttype);

                this.expectTokenAndPop(TokenKind.TOKEN_LPAREN);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.SomethingType).oftype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);
            }
            else {
                const stype = this.parseSomethingType(ttype);
                this.raiseErrorIf(ttype === undefined || !this.m_assembly.checkConcreteSubtype(stype, ttype), `Expected ${ttype?.tkey ?? "Something"} but got ${stype.tkey}`);

                this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.SomethingType).oftype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
            }
        }
        else {
            stype = ttype as $TypeInfo.SomethingType;
            vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.SomethingType).oftype), whistory);
        }

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(stype, chktype), `Expected ${chktype.tkey} but got ${stype.tkey}`);
        return [BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), stype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory), stype];
    }

    private parseOk(ttype: $TypeInfo.OkType | $TypeInfo.ResultType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        let vv = undefined;
        let stype: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;

        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (this.testToken(TokenKind.TOKEN_OK)) {
                this.popToken();
                stype = this.parseOkTypeComplete(undefined, ttype);

                this.expectTokenAndPop(TokenKind.TOKEN_LPAREN);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).ttype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);
            }
            else {
                const stype = this.parseOkType(ttype);
                this.raiseErrorIf(ttype === undefined || !this.m_assembly.checkConcreteSubtype(stype, ttype), `Expected ${ttype?.tkey ?? "Ok"} but got ${stype.tkey}`);

                this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).ttype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
            }
        }
        else {
            stype = ttype as $TypeInfo.OkType;
            vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).ttype), whistory);
        }

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(stype, chktype), `Expected ${chktype.tkey} but got ${stype.tkey}`);
        return [BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), stype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory), stype];
    }

    private parseErr(ttype: $TypeInfo.ErrorType | $TypeInfo.ResultType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        let vv = undefined;
        let stype: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;

        if (this.m_parsemode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (this.testToken(TokenKind.TOKEN_ERR)) {
                this.popToken();
                stype = this.parseErrTypeComplete(undefined, ttype);

                this.expectTokenAndPop(TokenKind.TOKEN_LPAREN);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).etype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);
            }
            else {
                const stype = this.parseErrType(ttype);
                this.raiseErrorIf(ttype === undefined || !this.m_assembly.checkConcreteSubtype(stype, ttype), `Expected ${ttype?.tkey ?? "Err"} but got ${stype.tkey}`);

                this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.OkType).etype), whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
            }
        }
        else {
            stype = ttype as $TypeInfo.ErrorType;
            vv = this.parseValue(this.lookupMustDefType((stype as $TypeInfo.ErrorType).etype), whistory);
        }

        this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(stype, chktype), `Expected ${chktype.tkey} but got ${stype.tkey}`);
        return [BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), stype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory), stype];
    }

    private parseMapEntry(ttype: $TypeInfo.MapEntryType, whistory: boolean, inmapdecl: boolean): BSQONParseResult {
        const keytype = this.lookupMustDefType(ttype.ktype);
        const valtype = this.lookupMustDefType(ttype.vtype);

        if(this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON || (inmapdecl && this.testToken(TokenKind.TOKEN_LBRACKET))) {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const k = this.parseValue(keytype, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const v = this.parseValue(valtype, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            return BSQONParseResultInfo.create([BSQONParseResultInfo.getParseValue(k, whistory), BSQONParseResultInfo.getParseValue(v, whistory)], ttype, [[BSQONParseResultInfo.getValueType(k, whistory), BSQONParseResultInfo.getHistory(k, whistory)], [BSQONParseResultInfo.getValueType(v, whistory), BSQONParseResultInfo.getHistory(v, whistory)]], whistory);
        }
        else {
            if(inmapdecl && !this.testToken(TokenKind.TOKEN_TYPE)) {
                const k = this.parseValue(keytype, whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_ENTRY);
                const v = this.parseValue(valtype, whistory);

                return BSQONParseResultInfo.create([BSQONParseResultInfo.getParseValue(k, whistory), BSQONParseResultInfo.getParseValue(v, whistory)], ttype, [[BSQONParseResultInfo.getValueType(k, whistory), BSQONParseResultInfo.getHistory(k, whistory)], [BSQONParseResultInfo.getValueType(v, whistory), BSQONParseResultInfo.getHistory(v, whistory)]], whistory);
            }
            else {
                const etype = this.parseType();
                this.raiseErrorIf(etype.tkey !== ttype.tkey, `Expected ${ttype.tkey} but got value of type ${etype.tkey}`);

                this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                const k = this.parseValue(keytype, whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
                const v = this.parseValue(valtype, whistory);
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                return BSQONParseResultInfo.create([BSQONParseResultInfo.getParseValue(k, whistory), BSQONParseResultInfo.getParseValue(v, whistory)], ttype, [[BSQONParseResultInfo.getValueType(k, whistory), BSQONParseResultInfo.getHistory(k, whistory)], [BSQONParseResultInfo.getValueType(v, whistory), BSQONParseResultInfo.getHistory(v, whistory)]], whistory);
            }
        }
    }

    private parseTuple(ttype: $TypeInfo.TupleType, whistory: boolean): BSQONParseResult {
        this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);

        if (this.testToken(TokenKind.TOKEN_RBRACKET)) {
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            this.raiseErrorIf(ttype.entries.length !== 0, `Expected ${ttype.entries.length} values but got []`);
            return BSQONParseResultInfo.create([], ttype, [], whistory);
        }
        else {
            let tvals: any[] = [];
            let ptree: [$TypeInfo.BSQType, any][] = [];

            let first = true;
            while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                if(first) {
                    first = false;
                }
                else {
                    this.popToken();
                }
                
                const entry = this.parseValue(this.lookupMustDefType(ttype.entries[tvals.length]), whistory);

                tvals.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
            }
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            this.raiseErrorIf(ttype.entries.length !== tvals.length, `Expected ${ttype.entries.length} values but got ${tvals.length}`);
            return BSQONParseResultInfo.create(tvals, ttype, ptree, whistory);
        }
    }

    private parseRecord(ttype: $TypeInfo.RecordType, whistory: boolean): BSQONParseResult {
        this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);

        if (this.testToken(TokenKind.TOKEN_RBRACE)) {
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

            this.raiseErrorIf(ttype.entries.length !== 0, `Expected ${Object.keys(ttype.entries).length} values but got {}`);
            return BSQONParseResultInfo.create({}, ttype, {}, whistory);
        }
        else {
            let tvals: {[k: string]: any} = {};
            let ptree: {[k: string]: [$TypeInfo.BSQType, any]} = {};
            let first = true;
            while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                if(first) {
                    first = false;
                }
                else {
                    this.popToken();
                }
                
                const pname = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;
                this.expectTokenAndPop(this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON ? TokenKind.TOKEN_COLON : TokenKind.TOKEN_EQUALS);

                const ptype = ttype.entries.find((ee) => ee.pname === pname);
                this.raiseErrorIf(ptype === undefined, `Unexpected property ${pname} in record`);

                const entry = this.parseValue(this.lookupMustDefType(ptype!.ptype), whistory);

                tvals[pname] = BSQONParseResultInfo.getParseValue(entry, whistory);
                ptree[pname] = [BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)];
            }
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

            this.raiseErrorIf(ttype.entries.length !== Object.keys(tvals).length, `Expected ${Object.keys(ttype.entries).length} values but got ${Object.keys(tvals).length}`);
            this.raiseErrorIf(ttype.entries.some((entry) => !(entry.pname in tvals)), `Expected property ${Object.keys(ttype.entries).filter((pname) => !(pname in tvals)).join(", ")} but not provided`);

            return BSQONParseResultInfo.create(Object.freeze(tvals), ttype, ptree, whistory);
        }
    }

    private parseEnum(ttype: $TypeInfo.EnumType, whistory: boolean): BSQONParseResult {
        const etype = this.parseType();
        this.expectTokenAndPop(TokenKind.TOKEN_COLON_COLON);
        const ename = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;

        this.raiseErrorIf(etype.tkey !== ttype.tkey, `Expected enum of type ${ttype.tkey} but got ${etype.tkey}::${ename}`);
        this.raiseErrorIf(!ttype.variants.includes(ename), `Enum ${ttype.tkey} does not contain value ${ename}`);

        return BSQONParseResultInfo.create(`${etype.tkey}::${ename}`, ttype, undefined, whistory);
    }
    
    private parseTypedecl(ttype: $TypeInfo.TypedeclType, whistory: boolean): BSQONParseResult {
        const vv = this.parseValue(this.lookupMustDefType(ttype.basetype), whistory);

        if (this.testAndPop_TypedeclUnder()) {
            const ntype = this.parseType();
            this.raiseErrorIf(ttype.tkey !== ntype.tkey, `Expected typedecl of type ${ttype.tkey} but got ${ntype.tkey}`);
        }

        if(ttype.hasvalidations) {
            this.m_typedeclChecks.push({ttype: ttype.tkey, tvalue: vv});
        }

        if(ttype.basetype.tkey === "String" || ttype.basetype.tkey === "ASCIIString") {
            if(ttype.optStringOfValidator !== undefined) {
                const vre = this.m_assembly.revalidators.get(ttype.optStringOfValidator);
                this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), vv as string), `Typedecl of string literal does not satisfy the required format: ${ttype.optStringOfValidator} (${vre})`);
            }
        }
        if(ttype.basetype.tkey === "Path" || ttype.basetype.tkey === "PathFragment" || ttype.basetype.tkey === "PathGlob") {
            this.raiseError("Path types are not IMPLEMENTED in typedecls");
        }

        return BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), ttype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory);
    }

    private parseStdEntity(ttype: $TypeInfo.StdEntityType, whistory: boolean): BSQONParseResult {
        if(!this.testToken(TokenKind.TOKEN_LBRACE)) {
            const etype = this.parseType();
            this.raiseErrorIf(etype.tkey !== ttype.tkey, `Expected entity of type ${ttype.tkey} but got ${etype.tkey}`);
        }
        this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);

        let tvals: {[k: string]: any} = {};
        let ptree: {[k: string]: [$TypeInfo.BSQType, any]} = {};
        if (this.testToken(TokenKind.TOKEN_RBRACE)) {
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

            this.raiseErrorIf(ttype.fields.length !== 0, `Expected ${ttype.fields.length} values but got {}`);
            return BSQONParseResultInfo.create({}, ttype, {}, whistory);
        }
        else {
            if(this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
                let first = true;
                while (first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if (first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    const ff = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;
                    const ffe = ttype.fields.find((f) => f.fname === ff);
                    this.raiseErrorIf(ffe === undefined, `Field ${ff} does not exist on type ${ttype.tkey}`);
                    
                    this.expectTokenAndPop(TokenKind.TOKEN_COLON);
                    const vv = this.parseValue(this.lookupMustDefType(ffe!.ftype), whistory);

                    tvals[ffe!.fname] = BSQONParseResultInfo.getParseValue(vv, whistory);
                    ptree[ffe!.fname] = [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)];
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                if(ttype.hasvalidations) {
                    this.m_stdentityChecks.push({ etype: ttype.tkey, evalue: tvals });
                }

                this.raiseErrorIf(ttype.fields.length !== Object.keys(tvals).length, `Expected ${ttype.fields.length} values but got ${Object.keys(tvals).length}`);
                return BSQONParseResultInfo.create(Object.freeze(tvals), ttype, ptree, whistory);
            }
            else {
                let ii = 0;
                while (ii === 0 || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if (ii !== 0) {
                        this.popToken();
                    }

                    if (ii >= ttype.fields.length) {
                        this.raiseError(`Expected ${ttype.fields.length} values but got ${ii}`);
                    }
                    const ff = ttype.fields[ii++];
                    const vv = this.parseValue(this.lookupMustDefType(ff.ftype), whistory);

                    tvals[ff.fname] = BSQONParseResultInfo.getParseValue(vv, whistory);
                    ptree[ff.fname] = [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)];
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                if(ttype.hasvalidations) {
                    this.m_stdentityChecks.push({ etype: ttype.tkey, evalue: tvals });
                }

                this.raiseErrorIf(ttype.fields.length !== Object.keys(tvals).length, `Expected ${ttype.fields.length} values but got ${Object.keys(tvals).length}`);
                return BSQONParseResultInfo.create(Object.freeze(tvals), ttype, ptree, whistory);
            }
        }
    }

    private parseList(ttype: $TypeInfo.ListType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        if(this.testToken(TokenKind.TOKEN_LBRACKET)) {
            this.raiseErrorIf(ttype === undefined, `Cannot use list [...] shorthand notation in ambigious context`);

            this.popToken();
            if(this.testToken(TokenKind.TOKEN_RBRACKET)) {
                this.popToken();

                return [BSQONParseResultInfo.create(IList<any>(), ttype as $TypeInfo.ListType, [], whistory), ttype as $TypeInfo.ListType];
            }
            else {
                let first = true;
                let vv: any[] = [];
                let ptree: [$TypeInfo.BSQType, any][] = [];
                while(first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if(first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    if(this.testToken(TokenKind.TOKEN_LDOTS)) {
                        const entry = this.parseValue(ttype as $TypeInfo.ListType, whistory);
                        vv.push(...(BSQONParseResultInfo.getParseValue(entry, whistory) as IList<any>));

                        if(whistory) {
                            ptree.push(...(BSQONParseResultInfo.getHistory(entry, whistory) as [$TypeInfo.BSQType, any][]));
                        }
                    }
                    else {
                        const entry = this.parseValue(this.lookupMustDefType((ttype as $TypeInfo.ListType).oftype), whistory);
                        vv.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                        ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
                    }
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

                return [BSQONParseResultInfo.create(IList<any>(vv), ttype as $TypeInfo.ListType, ptree, whistory), ttype as $TypeInfo.ListType];
            }
        }
        else {
            const ltype = this.parseListType(ttype);
            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(ltype, chktype), `Expected a type ${chktype.tkey} but got ${ltype.tkey}`);

            this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
            if(this.testToken(TokenKind.TOKEN_RBRACE)) {
                this.popToken();

                return [BSQONParseResultInfo.create(IList<any>(), ltype as $TypeInfo.ListType, [], whistory), ltype];
            }
            else {
                let first = true;
                let vv: any[] = [];
                let ptree: [$TypeInfo.BSQType, any][] = [];
                while(first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if(first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    if(this.testToken(TokenKind.TOKEN_LDOTS)) {
                        const entry = this.parseValue(ltype, whistory);
                        vv.push(...(BSQONParseResultInfo.getParseValue(entry, whistory) as IList<any>));

                        if(whistory) {
                            ptree.push(...(BSQONParseResultInfo.getHistory(entry, whistory) as [$TypeInfo.BSQType, any][]));
                        }
                    }
                    else {
                        const entry = this.parseValue(this.lookupMustDefType((ltype as $TypeInfo.ListType).oftype), whistory);
                        vv.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                        ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
                    }
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                return [BSQONParseResultInfo.create(IList<any>(vv), ltype, ptree, whistory), ltype];
            }
        }
    }

    private parseStack(ttype: $TypeInfo.StackType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        this.raiseError("Not implemented -- parseStack");
        return (undefined as any) as [BSQONParseResult, $TypeInfo.BSQType];
    }

    private parseQueue(ttype: $TypeInfo.QueueType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        this.raiseError("Not implemented -- parseQueue");
        return (undefined as any) as [BSQONParseResult, $TypeInfo.BSQType];
    }

    private parseSet(ttype: $TypeInfo.SetType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        this.raiseError("Not implemented -- parseSet");
        return (undefined as any) as [BSQONParseResult, $TypeInfo.BSQType];
    }

    private static genericKeyEq(k1: any, k2: any): boolean {
        if (k1 === k2) {
            return true;
        }
        else {
            const type1 = typeof k1;
            if(type1 !== "object") {
                return false;
            }
            else {
                if(k1 instanceof $Runtime.UnionValue) {
                    return k1.equals(k2);
                }
                else {
                    return k1.equalsBase(k2);
                }
            }
        }
    }

    private parseMap(ttype: $TypeInfo.MapType | undefined, chktype: $TypeInfo.BSQType, whistory: boolean): [BSQONParseResult, $TypeInfo.BSQType] {
        if(this.testToken(TokenKind.TOKEN_LBRACKET)) {
            this.raiseErrorIf(ttype === undefined, `Cannot use map {...} shorthand notation in ambigious context`);

            this.popToken();
            if(this.testToken(TokenKind.TOKEN_RBRACKET)) {
                this.popToken();

                return [BSQONParseResultInfo.create(IMap<any, any>(), ttype as $TypeInfo.MapType, [], whistory), ttype as $TypeInfo.MapType];
            }
            else {
                const metype = this.lookupMustDefType(`MapEntry<${(ttype as $TypeInfo.MapType).ktype}, ${(ttype as $TypeInfo.MapType).vtype}>`) as $TypeInfo.MapEntryType;

                let first = true;
                let vv: [any, any][] = [];
                let ptree: [$TypeInfo.BSQType, any][] = [];
                while(first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if(first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    if(this.testToken(TokenKind.TOKEN_LDOTS)) {
                        this.raiseError("... shorthand notation NOT IMPLEMENTED for maps yet");
                    }
                    else {
                        const entry = this.parseMapEntry(metype, whistory, true);

                        const kk = BSQONParseResultInfo.getParseValue(entry, whistory)[0];
                        this.raiseErrorIf(vv.some((v) => BSQONParser.genericKeyEq(kk, v[0])), `Duplicate key`);

                        vv.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                        ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
                    }
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

                return [BSQONParseResultInfo.create(IMap<any, any>(vv), ttype as $TypeInfo.MapType, ptree, whistory), ttype as $TypeInfo.MapType];
            }
        }
        else {
            const ltype = this.parseMapType(ttype);
            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(ltype, chktype), `Expected a type ${chktype.tkey} but got ${ltype.tkey}`);

            this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
            if(this.testToken(TokenKind.TOKEN_RBRACE)) {
                this.popToken();

                return [BSQONParseResultInfo.create(IMap<any, any>(), ltype as $TypeInfo.MapType, [], whistory), ltype];
            }
            else {
                const metype = this.lookupMustDefType(`MapEntry<${(ltype as $TypeInfo.MapType).ktype}, ${(ltype as $TypeInfo.MapType).vtype}>`) as $TypeInfo.MapEntryType;

                let first = true;
                let vv: [any, any][] = [];
                let ptree: [$TypeInfo.BSQType, any][] = [];
                while(first || this.testToken(TokenKind.TOKEN_COMMA)) {
                    if(first) {
                        first = false;
                    }
                    else {
                        this.popToken();
                    }

                    if(this.testToken(TokenKind.TOKEN_LDOTS)) {
                        this.raiseError("... shorthand notation NOT IMPLEMENTED for maps yet");
                    }
                    else {
                        const entry = this.parseMapEntry(metype, whistory, true);

                        const kk = BSQONParseResultInfo.getParseValue(entry, whistory)[0];
                        this.raiseErrorIf(vv.some((v) => BSQONParser.genericKeyEq(kk, v[0])), `Duplicate key`);

                        vv.push(BSQONParseResultInfo.getParseValue(entry, whistory));
                        ptree.push([BSQONParseResultInfo.getValueType(entry, whistory), BSQONParseResultInfo.getHistory(entry, whistory)]);
                    }
                }
                this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                return [BSQONParseResultInfo.create(IMap<any, any>(vv), ltype as $TypeInfo.MapType, ptree, whistory), ltype];
            }
        }
    }

    private parseValuePrimitive(ttype: $TypeInfo.PrimitiveType, whistory: boolean): BSQONParseResult {
        if(ttype.tkey === "None") {
            return this.parseNone(whistory);
        }
        else if(ttype.tkey === "Nothing") {
            return this.parseNothing(whistory);
        }
        else if(ttype.tkey === "Bool") {
            return this.parseBool(whistory);
        }
        else if(ttype.tkey === "Int") {
            return this.parseInt(whistory);
        }
        else if(ttype.tkey === "Nat") {
            return this.parseNat(whistory);
        }
        else if(ttype.tkey === "BigInt") {
            return this.parseBigInt(whistory);
        }
        else if(ttype.tkey === "BigNat") {
            return this.parseBigNat(whistory);
        }
        else if(ttype.tkey === "Rational") {
            return this.parseRational(whistory);
        }
        else if(ttype.tkey === "Float") {
            return this.parseFloat(whistory);
        }
        else if(ttype.tkey === "Decimal") {
            return this.parseDecimal(whistory);
        }
        else if(ttype.tkey === "String") {
            return this.parseString(whistory);
        }
        else if(ttype.tkey === "ASCIIString") {
            return this.parseASCIIString(whistory);
        }
        else if(ttype.tkey === "ByteBuffer") {
            return this.parseByteBuffer(whistory);
        }
        else if(ttype.tkey === "DateTime") {
            return this.parseDateTime(whistory);
        }
        else if(ttype.tkey === "UTCDateTime") {
            return this.parseUTCDateTime(whistory);
        }
        else if(ttype.tkey === "PlainDate") {
            return this.parsePlainDate(whistory);
        }
        else if(ttype.tkey === "PlainTime") {
            return this.parsePlainTime(whistory);
        }
        else if(ttype.tkey === "TickTime") {
            return this.parseTickTime(whistory);
        }
        else if(ttype.tkey === "LogicalTime") {
            return this.parseLogicalTime(whistory);
        }
        else if(ttype.tkey === "ISOTimeStamp") {
            return this.parseISOTimeStamp(whistory);
        }
        else if(ttype.tkey === "UUIDv4") {
            return this.parseUUIDv4(whistory);
        }
        else if(ttype.tkey === "UUIDv7") {
            return this.parseUUIDv7(whistory);
        }
        else if(ttype.tkey === "SHAContentHash") {
            return this.parseSHAContentHash(whistory);
        } 
        else if(ttype.tkey === "LatLongCoordinate") {
            return this.parseLatLongCoordinate(whistory);
        }
        else if(ttype.tkey === "Regex") {
            return this.parseRegex(whistory);
        }
        else {
            this.raiseError(`Unknown primitive type ${ttype.tkey}`);
        }
    }

    private parseValueDirect(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        if(ttype instanceof $TypeInfo.TupleType) {
            return this.parseTuple(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.RecordType) {
            return this.parseRecord(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.StdEntityType) {
            return this.parseStdEntity(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.EnumType) {
            return this.parseEnum(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.TypedeclType) {
            return this.parseTypedecl(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.StringOfType) {
            return this.parseStringOf(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.ASCIIStringOfType) {
            return this.parseASCIIStringOf(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.SomethingType) {
            return this.parseSomething(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.OkType) {
            return this.parseOk(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.ErrorType) {
            return this.parseErr(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.PathType) {
            return this.parsePath(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.PathFragmentType) {
            return this.parsePathFragment(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.PathGlobType) {
            return this.parsePathGlob(ttype, whistory);
        }
        else if(ttype instanceof $TypeInfo.ListType) {
            return this.parseList(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.StackType) {
            return this.parseStack(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.QueueType) {
            return this.parseQueue(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.SetType) {
            return this.parseSet(ttype, ttype, whistory)[0];
        }
        else if(ttype instanceof $TypeInfo.MapEntryType) {
            return this.parseMapEntry(ttype, whistory, false);
        }
        else if(ttype instanceof $TypeInfo.MapType) {
            return this.parseMap(ttype, ttype, whistory)[0];
        }
        else {
            this.raiseError(`Unknown type ${ttype.tkey}`);
        }
    }

    private parseValueConcept(ttype: $TypeInfo.ConceptType | $TypeInfo.ConceptSetType, whistory: boolean): BSQONParseResult {
        if (this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const tt = this.parseType();
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const vv = this.parseValue(tt, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            this.raiseErrorIf(!tt.isconcretetype, `Expected concrete type but got ${tt.tkey}`);
            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(tt, ttype), `Expected type ${ttype.tkey} but got ${tt.tkey}`);
            return BSQONParseResultInfo.create(new $Runtime.UnionValue(tt.tkey, BSQONParseResultInfo.getParseValue(vv, whistory)), tt, BSQONParseResultInfo.getHistory(vv, whistory), whistory);
        }
        else {
            let rv: BSQONParseResult = undefined;
            let rt: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;
            
            if (ttype instanceof $TypeInfo.OptionType) {
                if (this.testToken(TokenKind.TOKEN_NOTHING)) {
                    rv = this.parseNothing(whistory);
                    rt = this.lookupMustDefType("Nothing");
                }
                else {
                    [rv, rt] = this.parseSomething(ttype, ttype, whistory);
                }
            }
            else if (ttype instanceof $TypeInfo.ResultType) {
                if (this.testToken(TokenKind.TOKEN_OK) || this.testTokensWValue({kind: TokenKind.TOKEN_TYPE, value: "Result"}, {kind: TokenKind.TOKEN_COLON_COLON, value: "::"}, {kind: TokenKind.TOKEN_TYPE, value: "Ok"})) {
                    [rv, rt] = this.parseOk(ttype, ttype, whistory);
                }
                else if (this.testToken(TokenKind.TOKEN_ERR) || this.testTokensWValue({kind: TokenKind.TOKEN_TYPE, value: "Result"}, {kind: TokenKind.TOKEN_COLON_COLON, value: "::"}, {kind: TokenKind.TOKEN_TYPE, value: "Err"})) {
                    [rv, rt] = this.parseErr(ttype, ttype, whistory);
                }
                else {
                    const rtype = this.parseNominalType();
                    this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(rtype, ttype), `Expected result of type ${ttype.tkey} but got ${rtype.tkey}`);

                    if (rtype instanceof $TypeInfo.OkType) {
                        this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                        const vv = this.parseValue(this.lookupMustDefType(rtype.ttype), whistory);
                        this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                        rv = BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), rtype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory);
                        rt = rtype;
                    }
                    else {
                        this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
                        const vv = this.parseValue(this.lookupMustDefType((rtype as $TypeInfo.ErrorType).etype), whistory);
                        this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);

                        rv = BSQONParseResultInfo.create(BSQONParseResultInfo.getParseValue(vv, whistory), rtype, [BSQONParseResultInfo.getValueType(vv, whistory), BSQONParseResultInfo.getHistory(vv, whistory)], whistory);
                        rt = rtype;
                    }
                }
            }
            else if (ttype instanceof $TypeInfo.StdConceptType) {
                const tt = this.parseNominalType();
                this.raiseErrorIf(!(tt instanceof $TypeInfo.StdEntityType), `Expected std entity type but got ${tt.tkey}`);
                this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(tt, ttype), `Expected std entity of type ${ttype.tkey} but got ${tt.tkey}`);

                rv = this.parseStdEntity(tt as $TypeInfo.StdEntityType, whistory);
                rt = tt;
            }
            else if (ttype instanceof $TypeInfo.ConceptSetType) {
                const tt = this.parseNominalType();
                this.raiseErrorIf(!(tt instanceof $TypeInfo.StdEntityType), `Expected std entity type but got ${tt.tkey}`);
                this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(tt, ttype), `Expected std entity of type ${ttype.tkey} but got ${tt.tkey}`);

                rv = this.parseStdEntity(tt as $TypeInfo.StdEntityType, whistory);
                rt = tt;
            }
            else {
                this.raiseError(`Unknown concept type ${ttype.tkey}`);
            }

            return BSQONParseResultInfo.create(new $Runtime.UnionValue(rt.tkey, BSQONParseResultInfo.getParseValue(rv, whistory)), rt, BSQONParseResultInfo.getHistory(rv, whistory), whistory);
        }
    }

    private resolveRelaxedTypeMatch(oftags: $TypeInfo.BSQTypeTag[], opts: $TypeInfo.UnionType): $TypeInfo.BSQType | undefined {
        let tt: $TypeInfo.BSQType | undefined = undefined;
        if (opts.types.length === 1) {
            tt = this.lookupMustDefType(opts.types[0]);
        }
        else if(opts.types.length === 2 && opts.types.includes("None")) {
            tt = this.lookupMustDefType(opts.types[0] === "None" ? opts.types[1] : opts.types[0]);
        }   
        else {
            ; //do nothing
        }

        return (tt !== undefined && oftags.includes(tt.tag)) ? tt : undefined;
    }

    private isNoneableParse(ttype: $TypeInfo.UnionType): boolean {
        return ttype.types.length === 2 && ttype.types.includes("None");
    }

    private getNoneableRealType(ttype: $TypeInfo.UnionType): $TypeInfo.BSQType {
        return this.lookupMustDefType(ttype.types[0] === "None" ? ttype.types[1] : ttype.types[0]);
    }

    private parseValueSimple(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        if (ttype instanceof $TypeInfo.PrimitiveType) {
            return this.parseValuePrimitive(ttype, whistory);
        }
        else if ((ttype instanceof $TypeInfo.ConceptType) || (ttype instanceof $TypeInfo.ConceptSetType)) {
            return this.parseValueConcept(ttype, whistory);
        }
        else {
            return this.parseValueDirect(ttype, whistory);
        }
    }

    private parseValueUnion(ttype: $TypeInfo.UnionType, whistory: boolean): BSQONParseResult {
        //everyone has a none special format option
        if(this.testToken(TokenKind.TOKEN_NONE)) {
            const nonep = this.parseNone(whistory);
            return BSQONParseResultInfo.create(new $Runtime.UnionValue("None", BSQONParseResultInfo.getParseValue(nonep, whistory)), this.lookupMustDefType("None"), BSQONParseResultInfo.getHistory(nonep, whistory), whistory);
        }

        //Check for special nonable form as well "T | none"
        if(this.isNoneableParse(ttype)) {
            //from previous check we know that the type is not none
            const vtt = this.parseValueSimple(this.getNoneableRealType(ttype), whistory);
            return BSQONParseResultInfo.create(new $Runtime.UnionValue(this.getNoneableRealType(ttype).tkey, BSQONParseResultInfo.getParseValue(vtt, whistory)), this.getNoneableRealType(ttype), BSQONParseResultInfo.getHistory(vtt, whistory), whistory);
        }

        if (this.m_parsemode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const tt = this.parseType();
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const vv = this.parseValue(tt, whistory);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);

            this.raiseErrorIf(!tt.isconcretetype, `Expected concrete type but got ${tt.tkey}`);
            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(tt, ttype), `Expected type ${ttype.tkey} but got ${tt.tkey}`);
            return BSQONParseResultInfo.create(new $Runtime.UnionValue(tt.tkey, BSQONParseResultInfo.getParseValue(vv, whistory)), tt, BSQONParseResultInfo.getHistory(vv, whistory), whistory);
        }
        else {
            //it isn't none so now we start looking at prefixes
            const tk = this.peekToken()?.kind ?? "EOF";

            let rv: BSQONParseResult = undefined;
            let rt: $TypeInfo.BSQType = $TypeInfo.UnresolvedType.singleton;

            if(tk === TokenKind.TOKEN_NOTHING) {
                rv = this.parseNothing(whistory);
                rt = this.lookupMustDefType("Nothing");
            }
            else if(tk === TokenKind.TOKEN_SOMETHING) {
                const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_SOMETHING, $TypeInfo.BSQTypeTag.TYPE_OPTION], ttype);
                [rv, rt] = this.parseSomething(oftt as ($TypeInfo.SomethingType | $TypeInfo.OptionType | undefined), ttype, whistory);
            }
            else if(tk === TokenKind.TOKEN_OK) {
                const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_OK, $TypeInfo.BSQTypeTag.TYPE_RESULT], ttype);
                [rv, rt] = this.parseOk(oftt as ($TypeInfo.OkType | $TypeInfo.ResultType | undefined), ttype, whistory);
            }
            else if(tk === TokenKind.TOKEN_ERR) {
                const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_ERROR, $TypeInfo.BSQTypeTag.TYPE_RESULT], ttype);
                [rv, rt] = this.parseErr(oftt as ($TypeInfo.ErrorType | $TypeInfo.ResultType | undefined), ttype, whistory);
            }
            else if(tk === TokenKind.TOKEN_TYPE) {
                const ptt = this.peekToken()!.value;
                if(ptt === "Something") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_SOMETHING, $TypeInfo.BSQTypeTag.TYPE_OPTION], ttype);
                    [rv, rt] = this.parseSomething(oftt as ($TypeInfo.SomethingType | $TypeInfo.OptionType | undefined), ttype, whistory);
                }
                else if(ptt === "Result") {
                    if(this.testTokensWValue({kind: TokenKind.TOKEN_TYPE, value: "Result"}, {kind: TokenKind.TOKEN_COLON_COLON, value: "::"}, {kind: TokenKind.TOKEN_TYPE, value: "Ok"})) {
                        const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_OK, $TypeInfo.BSQTypeTag.TYPE_RESULT], ttype);
                        [rv, rt] = this.parseOk(oftt as ($TypeInfo.OkType | $TypeInfo.ResultType | undefined), ttype, whistory);
                    }
                    else if(this.testTokensWValue({kind: TokenKind.TOKEN_TYPE, value: "Result"}, {kind: TokenKind.TOKEN_COLON_COLON, value: "::"}, {kind: TokenKind.TOKEN_TYPE, value: "Err"})) {
                        const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_ERROR, $TypeInfo.BSQTypeTag.TYPE_RESULT], ttype);
                        [rv, rt] = this.parseErr(oftt as ($TypeInfo.ErrorType | $TypeInfo.ResultType | undefined), ttype, whistory);
                    }
                    else {
                        rt = this.peekType();
                        if(rt instanceof $TypeInfo.OkType) {
                            rv = this.parseOk(rt, ttype, whistory)[0];
                        }
                        else {
                            rv = this.parseErr(rt as $TypeInfo.ErrorType, ttype, whistory)[0];
                        }
                    }
                }
                else if(ptt === "List") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_LIST], ttype);
                    [rv, rt] = this.parseList(oftt as ($TypeInfo.ListType | undefined), ttype, whistory);
                }
                else if(ptt === "Stack") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_STACK], ttype);
                    [rv, rt] = this.parseStack(oftt as ($TypeInfo.StackType | undefined), ttype, whistory);
                }
                else if(ptt === "Queue") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_QUEUE], ttype);
                    [rv, rt] = this.parseQueue(oftt as ($TypeInfo.QueueType | undefined), ttype, whistory);
                }
                else if(ptt === "Set") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_SET], ttype);
                    [rv, rt] = this.parseSet(oftt as ($TypeInfo.SetType | undefined), ttype, whistory);
                }
                else if(ptt === "Map") {
                    const oftt = this.resolveRelaxedTypeMatch([$TypeInfo.BSQTypeTag.TYPE_MAP], ttype);
                    [rv, rt] = this.parseMap(oftt as ($TypeInfo.MapType | undefined), ttype, whistory);
                }
                else {
                    const tt = this.peekType();
                    this.raiseErrorIf(!tt.isconcretetype, `Expected concrete type but got ${tt.tkey}`);

                    rv = this.parseValue(tt, whistory);
                    rt = tt;
                }
            }
            else if(tk === TokenKind.TOKEN_LPAREN) {
                this.popToken();
                const tt = this.parseType();
                this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);

                rv = this.parseValue(tt, whistory);
                rt = tt;
            }
            //Now are some (probably) common prefix/mistakes that we can warn about
            else if(tk === TokenKind.TOKEN_LBRACE) {
                this.raiseError(`Unexpected token ${tk} -- in ambigous position records need to be prefixed with a (type) and entities need a full constructor`);
            }
            else if(tk === TokenKind.TOKEN_LBRACKET) {
                this.raiseError(`Unexpected token ${tk} -- in ambigous position tuples/lists/etc. need to be prefixed with a (type)`);
            }
            else {
                let tt: string = "[UnresolvedType]";

                if(this.testToken(TokenKind.TOKEN_TRUE) || this.testToken(TokenKind.TOKEN_FALSE)) {
                    rv = this.parseBool(whistory);
                    tt = "Bool";
                }
                else if(this.testToken(TokenKind.TOKEN_NAT)) {
                    rv = this.parseNat(whistory);
                    tt = "Nat";
                }
                else if(this.testToken(TokenKind.TOKEN_INT)) {
                    rv = this.parseInt(whistory);
                    tt = "Int";
                }
                else if(this.testToken(TokenKind.TOKEN_BIG_NAT)) {
                    rv = this.parseBigNat(whistory);
                    tt = "BigNat";
                }
                else if(this.testToken(TokenKind.TOKEN_BIG_INT)) {
                    rv = this.parseBigInt(whistory);
                    tt = "BigInt";
                }
                else if(this.testToken(TokenKind.TOKEN_FLOAT)) {
                    rv = this.parseFloat(whistory);
                    tt = "Float";
                }
                else if(this.testToken(TokenKind.TOKEN_DECIMAL)) {
                    rv = this.parseDecimal(whistory);
                    tt = "Decimal";
                }
                else if(this.testToken(TokenKind.TOKEN_RATIONAL)) {
                    rv = this.parseRational(whistory);
                    tt = "Rational";
                }
                else if(this.testTokens(TokenKind.TOKEN_STRING, TokenKind.TOKEN_TYPE)) {
                    [rv, tt] = this.parseStringOfWithType(whistory);
                }
                else if(this.testTokens(TokenKind.TOKEN_ASCII_STRING, TokenKind.TOKEN_TYPE)) {
                    [rv, tt] = this.parseASCIIStringOfWithType(whistory);
                }
                else if(this.testToken(TokenKind.TOKEN_STRING)) {
                    rv = this.parseString(whistory);
                    tt = "String";
                }
                else if(this.testToken(TokenKind.TOKEN_ASCII_STRING)) {
                    rv = this.parseASCIIString(whistory);
                    tt = "ASCIIString";
                }
                else if(this.testToken(TokenKind.TOKEN_BYTE_BUFFER)) {
                    rv = this.parseByteBuffer(whistory);
                    tt = "ByteBuffer";
                }
                else if(this.testToken(TokenKind.TOKEN_REGEX)) {
                    rv = this.parseRegex(whistory);
                    tt = "Regex";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_DATE_TIME)) {
                    rv = this.parseDateTime(whistory);
                    tt = "DateTime";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_UTC_DATE_TIME)) {
                    rv = this.parseUTCDateTime(whistory);
                    tt = "UTCDateTime";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_DATE)) {
                    rv = this.parsePlainDate(whistory);
                    tt = "Date";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_TIME)) {
                    rv = this.parsePlainTime(whistory);
                    tt = "Time";
                }
                else if(this.testToken(TokenKind.TOKEN_TICK_TIME)) {
                    rv = this.parseTickTime(whistory);
                    tt = "TickTime";
                }
                else if(this.testToken(TokenKind.TOKEN_LOGICAL_TIME)) {
                    rv = this.parseLogicalTime(whistory);
                    tt = "LogicalTime";
                }
                else if(this.testToken(TokenKind.TOKEN_ISO_TIMESTAMP)) {
                    rv = this.parseISOTimeStamp(whistory);
                    tt = "Timestamp";
                }
                else if(this.testToken(TokenKind.TOKEN_UUID)) {
                    if(this.peekToken()!.value.startsWith("uuid4{")) {
                        rv = this.parseUUIDv4(whistory);
                        tt = "UUIDv4";
                    }
                    else {
                        rv = this.parseUUIDv7(whistory);
                        tt = "UUIDv7";
                    }
                }
                else if(this.testToken(TokenKind.TOKEN_SHA_HASH)) {
                    rv = this.parseSHAContentHash(whistory);
                    tt = "SHAHash";
                }
                else if(this.testToken(TokenKind.TOKEN_PATH_ITEM)) {
                    this.raiseError("PATH ITEMS ARE NOT IMPLEMENTED YET!!!");
                }
                else {
                    this.raiseError(`Expected a primitive value but got ${tk}`);
                }

                if(this.testAndPop_TypedeclUnder()) {
                    const tdtype = this.parseType();
                    this.raiseErrorIf(!(tdtype instanceof $TypeInfo.TypedeclType), `Expected a typedecl type but got ${tdtype.tkey}`);
                    this.raiseErrorIf((tdtype as $TypeInfo.TypedeclType).basetype !== tt, `Typedecl has a basetype of ${tdtype.tkey} but got ${tt}`);

                    tt = tdtype.tkey;

                    if((tdtype as $TypeInfo.TypedeclType).optStringOfValidator !== undefined) {
                        const vre = this.m_assembly.revalidators.get((tdtype as $TypeInfo.TypedeclType).optStringOfValidator!);
                        this.raiseErrorIf(vre === undefined || !$Runtime.acceptsString(vre.slice(1, -1), tt), `Typedecl string literal does not satisfy the required format: ${(tdtype as $TypeInfo.TypedeclType).optStringOfValidator!} (${vre})`);
                    }

                    if((tdtype as $TypeInfo.TypedeclType).optPathOfValidator !== undefined) {
                        this.raiseError("PATH ITEMS ARE NOT IMPLEMENTED YET!!!");
                    }

                    if((tdtype as $TypeInfo.TypedeclType).hasvalidations) {
                        this.m_typedeclChecks.push({ttype: tt, tvalue: rv});
                    }
                }

                rt = this.lookupMustDefType(tt);
            }

            this.raiseErrorIf(!this.m_assembly.checkConcreteSubtype(rt, ttype), `Value is not of type ${ttype.tkey} -- got ${rt.tkey}`);   
            return BSQONParseResultInfo.create(new $Runtime.UnionValue(rt.tkey, BSQONParseResultInfo.getParseValue(rv, whistory)), rt, BSQONParseResultInfo.getHistory(rv, whistory), whistory);
        }
    }

    private parseValue(ttype: $TypeInfo.BSQType, whistory: boolean): BSQONParseResult {
        if(this.testTokens(TokenKind.TOKEN_LPAREN, TokenKind.TOKEN_LET)) {
            this.popToken();
            this.popToken();

            const vname = this.expectTokenAndPop(TokenKind.TOKEN_PROPERTY).value;
            this.expectTokenAndPop(TokenKind.TOKEN_COLON);
            const vtype = this.parseType();
            this.expectTokenAndPop(TokenKind.TOKEN_EQUALS);
            const vvalue = this.parseValue(vtype, true);
            
            this.raiseErrorIf(this.m_refs.has(vname), `Duplicate let binding ${vname}`);
            this.m_refs.set(vname, [BSQONParseResultInfo.getParseValue(vvalue, true), BSQONParseResultInfo.getValueType(vvalue, true), BSQONParseResultInfo.getHistory(vvalue, true)]);

            this.expectTokenAndPop(TokenKind.TOKEN_IN);

            const vv = this.parseExpression(ttype, whistory);

            this.expectTokenAndPop(TokenKind.TOKEN_RPAREN);

            this.m_refs.delete(vname);
            return vv;
        }
        else if(this.testTokens(TokenKind.TOKEN_SRC) || this.testTokens(TokenKind.TOKEN_REFERENCE)) {
            return this.parseExpression(ttype, whistory);
        }
        else {
            if (ttype instanceof $TypeInfo.UnionType) {
                return this.parseValueUnion(ttype, whistory);
            }
            else {
                return this.parseValueSimple(ttype, whistory);
            }
        }
    }

    static parse(input: string, ttype: $TypeInfo.BSQTypeKey, defaultns: string, importmap: Map<string, string>, assembly: $TypeInfo.AssemblyInfo, mode: $Runtime.NotationMode, srcbind: [any, $TypeInfo.BSQType, any] | undefined): {result: any, entityChecks: {etype: $TypeInfo.BSQTypeKey, evalue: object}[], typedeclChecks: {ttype: $TypeInfo.BSQTypeKey, tvalue: any}[]} {
        const parser = new BSQONParser(mode, defaultns, importmap, assembly, input, srcbind);
        const result = parser.parseValue(parser.lookupMustDefType(ttype), false);

        return {result: result, entityChecks: parser.m_stdentityChecks, typedeclChecks: parser.m_typedeclChecks};
    }

    static parseValueStd(input: string, ttype: $TypeInfo.BSQTypeKey, defaultns: string, assembly: $TypeInfo.AssemblyInfo): any {
        const parser = new BSQONParser($Runtime.NotationMode.NOTATION_MODE_BSQON, defaultns, new Map<string, string>(), assembly, input, undefined);

        const rr = parser.parseValue(parser.lookupMustDefType(ttype), false);
        return rr;
    }

    static parseInputsStd(input: string, ttypes: $TypeInfo.BSQTypeKey[], defaultns: string, assembly: $TypeInfo.AssemblyInfo): {result: any[], entityChecks: {etype: $TypeInfo.BSQTypeKey, evalue: object}[], typedeclChecks: {ttype: $TypeInfo.BSQTypeKey, tvalue: any}[]} {
        const parser = new BSQONParser($Runtime.NotationMode.NOTATION_MODE_BSQON, defaultns, new Map<string, string>(), assembly, input, undefined);

        let result: any[] = [];
        for(let i = 0; i < ttypes.length; ++i) {
            const rr = parser.parseValue(parser.lookupMustDefType(ttypes[i]), false);
            result.push(rr);
        }

        return {result: result, entityChecks: parser.m_stdentityChecks, typedeclChecks: parser.m_typedeclChecks};
    }*/
    };
}
