import { IRCRegex, IRURegex, IRSourceInfo, emitTypeKey, parseTypeKey } from "./irsupport.js";
import { IRDashResultTypeSignature, IREListTypeSignature, IRFormatTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature } from "./irtype.js";
import { IRBody, IRImmediateExpression, IRLiteralCRegexExpression, IRLiteralFormatCStringExpression, IRLiteralFormatStringExpression, IRLiteralUnicodeRegexExpression, IRSimpleExpression, IRStatement } from "./irbody.js";

import { BAPILexer, BAPITokenKind, parseListOf } from "./irlexer.js";

import assert from "node:assert";

abstract class IRConditionDecl {
    readonly file: string;
    readonly sinfo: IRSourceInfo;

    readonly diagnosticTag: string | undefined;
    
    readonly stmts: IRStatement[];
    readonly value: IRSimpleExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, stmts: IRStatement[], value: IRSimpleExpression) {
        this.file = file;
        this.sinfo = sinfo;
        
        this.diagnosticTag = diagnosticTag;

        this.stmts = stmts;
        this.value = value;
    }
}

class IRPreConditionDecl extends IRConditionDecl {
    readonly ikey: string;
    readonly requiresidx: number;
    
    readonly issoft: boolean;

    constructor(file: string, sinfo: IRSourceInfo, tag: string | undefined, ikey: string, requiresidx: number, issoft: boolean, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.ikey = ikey;
        this.requiresidx = requiresidx;
        this.issoft = issoft;
    }
}

class IRPostConditionDecl extends IRConditionDecl {
    readonly ikey: string;
    readonly ensuresidx: number;
    
    readonly issoft: boolean;
    
    constructor(file: string, sinfo: IRSourceInfo, tag: string | undefined, ikey: string, ensuresidx: number, issoft: boolean, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.ikey = ikey;
        this.ensuresidx = ensuresidx;
        this.issoft = issoft;
    }
}

class IRInvariantDecl extends IRConditionDecl {
    readonly tkey: string;
    readonly invariantidx: number;
    
    constructor(file: string, sinfo: IRSourceInfo, tag: string | undefined, tkey: string, invariantidx: number, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.tkey = tkey;
        this.invariantidx = invariantidx;
    }
}

class IRValidateDecl extends IRConditionDecl {
    readonly tkey: string;
    readonly validateidx: number;
    
    constructor(file: string, sinfo: IRSourceInfo, tag: string | undefined, tkey: string, validateidx: number, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.tkey = tkey;
        this.validateidx = validateidx;
    }
}

class IRDeclarationDocString {
    readonly text: string;

    constructor(text: string) {
        this.text = text;
    }
}

class IRDeclarationMetaTag {
    readonly name: string;
    readonly tags: {enumType: IRTypeSignature, tag: string}[];

    constructor(name: string, tags: {enumType: IRTypeSignature, tag: string}[]) {
        this.name = name;
        this.tags = tags;
    }
}

class IRConstantDecl {
    readonly ckey: string;

    readonly declaredType: IRTypeSignature;
    readonly stmts: IRStatement[];
    readonly value: IRSimpleExpression;

    readonly docstr: IRDeclarationDocString | undefined;

    constructor(ckey: string, declaredType: IRTypeSignature, stmts: IRStatement[], value: IRSimpleExpression, docstr: IRDeclarationDocString | undefined) {
        this.ckey = ckey;
        this.declaredType = declaredType;
        this.stmts = stmts;
        this.value = value;
        this.docstr = docstr;
    }
}

class IRInvokeParameterDecl {
    readonly name: string;
    readonly type: IRTypeSignature;
    readonly pkind: "ref" | "out" | "out?" | "inout" | undefined;
    readonly skind: "lcapture" | "this" | "self" | undefined;

    readonly defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined;
    
    constructor(name: string, type: IRTypeSignature, pkind: "ref" | "out" | "out?" | "inout" | undefined, skind: "lcapture" | "this" | "self" | undefined, defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined) {
        this.name = name;
        this.type = type;
        this.pkind = pkind;
        this.skind = skind;
        this.defaultValue = defaultValue;
    }
}

abstract class IRInvokeMetaDecl {
    readonly ikey: string;

    readonly recursive: "recursive" | "recursive?" | undefined;
    readonly params: IRInvokeParameterDecl[];
    readonly resultType: IRTypeSignature;

    readonly preconditions: IRPreConditionDecl[];
    readonly postconditions: IRPostConditionDecl[];

    readonly docstr: IRDeclarationDocString | undefined;

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo) {
        this.ikey = ikey;
        this.recursive = recursive;
        this.params = params;
        this.resultType = resultType;
        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.docstr = docstr;
        this.file = file;
        this.sinfo = sinfo;
    }
}

class IRTestAssociation {
    readonly file: string | undefined;
    readonly ns: string | undefined;
    readonly ontype: string | undefined;
    readonly onmember: string | undefined;

    constructor(file: string | undefined, ns: string | undefined, ontype: string | undefined, onmember: string | undefined) {
        this.file = file;
        this.ns = ns;
        this.ontype = ontype;
        this.onmember = onmember;
    }

    isMatchWith(tmatch: IRTestAssociation): boolean {
        if(tmatch.file !== undefined && this.file !== tmatch.file) {
            return false;
        }

        if(tmatch.ns !== undefined && this.ns !== tmatch.ns) {
            return false;
        }

        if(tmatch.ontype !== undefined && this.ontype !== tmatch.ontype) {
            return false;
        }

        if(tmatch.onmember !== undefined && this.onmember !== tmatch.onmember) {
            return false;
        }

        return true;
    }
}

class IRTestDecl extends IRInvokeMetaDecl {
    readonly testkind: "errtest" | "chktest";
    readonly association: IRTestAssociation[] | undefined;

    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, testkind: "errtest" | "chktest", association: IRTestAssociation[] | undefined, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.testkind = testkind;
        this.association = association;
        this.body = body;
    }
}

class IRExampleDecl extends IRInvokeMetaDecl {
    readonly association: IRTestAssociation[] | undefined;

    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, association: IRTestAssociation[] | undefined, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.association = association;
        this.body = body;
    }
} 

class IRInvokeDecl extends IRInvokeMetaDecl {
    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.body = body;
    }
}

class IRTaskActionDecl extends IRInvokeMetaDecl {
    readonly body: IRBody;

    constructor(ikey: string, recursive: "recursive" | "recursive?" | undefined, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, body: IRBody) {
        super(ikey, recursive, params, resultType, preconditions, postconditions, docstr, file, sinfo);
        this.body = body;
    }
}

class IRMemberFieldDecl {
    readonly fkey: string;

    readonly enclosingType: IRNominalTypeSignature;
    readonly fname: string;
    readonly declaredType: IRTypeSignature;
    readonly defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined;

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    constructor(fkey: string, enclosingType: IRNominalTypeSignature, fname: string, declaredType: IRTypeSignature, defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[]) {
        this.fkey = fkey;
        this.enclosingType = enclosingType;
        this.fname = fname;
        this.declaredType = declaredType;
        this.defaultValue = defaultValue;

        this.docstr = docstr;
        this.metatags = metatags;
    }
}

abstract class IRAbstractNominalTypeDecl {
    readonly tkey: string;

    readonly invariants: IRInvariantDecl[];
    readonly validates: IRValidateDecl[];
    readonly fields: IRMemberFieldDecl[];

    readonly etag: "std" | "status" | "event";

    readonly saturatedProvides: IRTypeSignature[];
    readonly saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[];

    readonly allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[];
    readonly allValidates: { containingtype: IRNominalTypeSignature, ii: number }[];
    
    //TODO vtable info here

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        this.tkey = tkey;
        this.invariants = invariants;
        this.validates = validates;
        this.fields = fields;
        this.etag = etag;
        this.saturatedProvides = saturatedProvides;
        this.saturatedBFieldInfo = saturatedBFieldInfo;
        this.allInvariants = allInvariants;
        this.allValidates = allValidates;
        this.docstr = docstr;
        this.metatags = metatags;

        //TODO vtable info here

        this.file = file;
        this.sinfo = sinfo;
    }

    abstract getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[];

    abstract toBAPI(): string;

    static parseBAPI(lexer: BAPILexer): IRAbstractNominalTypeDecl {
        const tok = lexer.peekToken();
        if(tok.kind !== BAPITokenKind.TypeIdentifier) {
            throw new Error(`Unexpected token ${tok.value} when parsing IRAbstractNominalTypeDecl`);
        }

        const ttypekey = tok.value;
        if(ttypekey === 'Assembly::EnumTypeDecl') {
            return IREnumTypeDecl.parseBAPIAsIREnumTypeDecl(lexer);
        }
        else if(ttypekey === 'Assembly::TypedeclSimpleTypeDecl') {
            return IRTypedeclTypeDecl.parseBAPIAsIRTypedeclTypeDecl(lexer);
        }
        else if(ttypekey === 'Assembly::TypedeclBoundedTypeDecl') {
            return IRTypedeclTypeDecl.parseBAPIAsIRTypedeclTypeDecl(lexer);
        }
        else if(ttypekey === 'Assembly::TypedeclCStringDecl') {
            return IRTypedeclCStringDecl.parseBAPIAsIRTypedeclCStringDecl(lexer);
        }
        else if(ttypekey === 'Assembly::TypedeclStringDecl') {
            return IRTypedeclStringDecl.parseBAPIAsIRTypedeclStringDecl(lexer);
        }
        else if(ttypekey === 'Assembly::PrimitiveEntityTypeDecl') {
            return IRPrimitiveEntityTypeDecl.parseBAPIAsIRPrimitiveEntityTypeDecl(lexer);
        }
        else {
            throw new Error(`Unexpected token ${tok.value} when parsing IRAbstractNominalTypeDecl`);
        }
    }

    toBAPI_IRAbstractNominalTypeDecl(): string {
        return [
            emitTypeKey(this.tkey),

            //readonly invariants: IRInvariantDecl[];
            //readonly validates: IRValidateDecl[];
            //readonly fields: IRMemberFieldDecl[];

            //readonly etag: "std" | "status" | "event";

            //readonly saturatedProvides: IRTypeSignature[];
            //readonly saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[];

            //readonly allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[];
            //readonly allValidates: { containingtype: IRNominalTypeSignature, ii: number }[];
    
            //TODO vtable info here

            //readonly docstr: IRDeclarationDocString | undefined;
            //readonly metatags: IRDeclarationMetaTag[];

            `'${this.file}'`,
            this.sinfo.toBAPI()
        ].join(", ");
    }

    static parseBAPI_IRAbstractNominalTypeDecl(lexer: BAPILexer): { tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo } {
        const tkey = lexer.parseTypeIdentifier();
        lexer.ensureAndConsumeSymbol(',');

        const file = lexer.ensureAndConsumeToken(BAPITokenKind.CStringLiteral).slice(1, -1);
        lexer.ensureAndConsumeSymbol(',');
        const sinfo = IRSourceInfo.parseBAPI(lexer);
        return { tkey, invariants: [], validates: [], fields: [], etag: "std", saturatedProvides: [], saturatedBFieldInfo: [], allInvariants: [], allValidates: [], docstr: undefined, metatags: [], file, sinfo };
    }
}

abstract class IRAbstractEntityTypeDecl extends IRAbstractNominalTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }

    toBAPI_IRAbstractEntityTypeDecl(): string {
        return this.toBAPI_IRAbstractNominalTypeDecl();
    }

    static parseBAPI_IRAbstractEntityTypeDecl(lexer: BAPILexer): { tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo } {
        return IRAbstractNominalTypeDecl.parseBAPI_IRAbstractNominalTypeDecl(lexer);
    }
}

class IREnumTypeDecl extends IRAbstractEntityTypeDecl {
    readonly members: string[];

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, members: string[]) {
        super(tkey, [], [], [], "std", [], [], [], [], docstr, [], file, sinfo);
        this.members = members;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [];
    }

    override toBAPI(): string {
        return `Assembly::IREnumTypeDecl{${this.toBAPI_IRAbstractEntityTypeDecl()}, List<CString>{${this.members.map(m => `'${m}'`).join(", ")}}}`;
    }

    static parseBAPIAsIREnumTypeDecl(lexer: BAPILexer): IREnumTypeDecl {
        lexer.consumeToken(); //Assembly::IREnumTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractEntityTypeDecl.parseBAPI_IRAbstractEntityTypeDecl(lexer);
        const members = parseListOf<string>(lexer, '{', '}', ',', (ll) => ll.ensureAndConsumeToken(BAPITokenKind.CStringLiteral).slice(1, -1));
        lexer.ensureAndConsumeSymbol("}");

        return new IREnumTypeDecl(etdfields.tkey, etdfields.docstr, etdfields.file, etdfields.sinfo, members);
    }
}

class IRTypedeclTypeDecl extends IRAbstractEntityTypeDecl {
    readonly valuetype: IRTypeSignature;
    readonly iskeytype: boolean;
    readonly isnumerictype: boolean;
   
    readonly rngchk: {min: IRImmediateExpression | undefined, max: IRImmediateExpression | undefined} | undefined;

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, valuetype: IRTypeSignature, iskeytype: boolean, isnumerictype: boolean, rngchk: {min: IRImmediateExpression | undefined, max: IRImmediateExpression | undefined} | undefined) {
        super(tkey, invariants, validates, [], "std", saturatedProvides, [], allInvariants, allValidates, docstr, metatags, file, sinfo);
        this.valuetype = valuetype;
        this.iskeytype = iskeytype;
        this.isnumerictype = isnumerictype;
        this.rngchk = rngchk;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [];
    }

    toBAPI_RNGCheck(): string {
        assert(this.rngchk !== undefined, "RNGCheck is undefined");

        const minstr = this.rngchk.min !== undefined ? `some(${this.rngchk.min.toBAPI()})` : 'none';
        const maxstr = this.rngchk.max !== undefined ? `some(${this.rngchk.max.toBAPI()})` : 'none';

        return `Assembly::TypedeclRangeCheck{${minstr}, ${maxstr}}`;
    }

    static parseBAPI_RNGCheck(lexer: BAPILexer): {min: IRImmediateExpression | undefined, max: IRImmediateExpression | undefined} {
        lexer.consumeToken(); //Assembly::TypedeclRangeCheck
        lexer.ensureAndConsumeSymbol("{");
        
        let minexpr: IRImmediateExpression | undefined = undefined;
        const mintok = lexer.consumeToken();
        if(mintok.kind !== BAPITokenKind.NoneLiteral) {
            lexer.ensureAndConsumeSymbol("(");
            minexpr = IRImmediateExpression.parseBAPIAsIRImmediateExpression(lexer);
            lexer.ensureAndConsumeSymbol(")");
        }

        lexer.ensureAndConsumeSymbol(",");

        let maxexpr: IRImmediateExpression | undefined = undefined;
        const maxtok = lexer.consumeToken();
        if(maxtok.kind !== BAPITokenKind.NoneLiteral) {
            lexer.ensureAndConsumeSymbol("(");
            maxexpr = IRImmediateExpression.parseBAPIAsIRImmediateExpression(lexer);
            lexer.ensureAndConsumeSymbol(")");
        }

        lexer.ensureAndConsumeSymbol("}");

        return {min: minexpr, max: maxexpr};
    }

    override toBAPI(): string {
        if(this.rngchk === undefined) {
            return `Assembly::TypedeclSimpleTypeDecl{${this.toBAPI_IRAbstractEntityTypeDecl()}, ${this.valuetype.toBAPI()}, ${this.iskeytype}, ${this.isnumerictype}}`;
        }
        else {
            return `Assembly::TypedeclBoundedTypeDecl{${this.toBAPI_IRAbstractEntityTypeDecl()}, ${this.valuetype.toBAPI()}, ${this.iskeytype}, ${this.isnumerictype}, ${this.toBAPI_RNGCheck()}}`;
        }
    }

    static parseBAPIAsIRTypedeclTypeDecl(lexer: BAPILexer): IRTypedeclTypeDecl {
        const tok = lexer.consumeToken();

        const etdfields = IRAbstractEntityTypeDecl.parseBAPI_IRAbstractEntityTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol(",");
        const valuetype = IRTypeSignature.parseBAPI(lexer);
        lexer.ensureAndConsumeSymbol(",");
        const ikeytype = lexer.consumeToken().kind === BAPITokenKind.TrueLiteral;
        lexer.ensureAndConsumeSymbol(",");
        const inumerictype = lexer.consumeToken().kind === BAPITokenKind.TrueLiteral;

        if(tok.value === 'Assembly::TypedeclSimpleTypeDecl') {
            lexer.ensureAndConsumeSymbol("}");

            return new IRTypedeclTypeDecl(etdfields.tkey, etdfields.invariants, etdfields.validates, etdfields.saturatedProvides, etdfields.allInvariants, etdfields.allValidates, etdfields.docstr, etdfields.metatags, etdfields.file, etdfields.sinfo, valuetype, ikeytype, inumerictype, undefined);
        }
        else if(tok.value === 'Assembly::TypedeclBoundedTypeDecl') {
            lexer.ensureAndConsumeSymbol(",");
            const rngchk = IRTypedeclTypeDecl.parseBAPI_RNGCheck(lexer);
            lexer.ensureAndConsumeSymbol("}");

            return new IRTypedeclTypeDecl(etdfields.tkey, etdfields.invariants, etdfields.validates, etdfields.saturatedProvides, etdfields.allInvariants, etdfields.allValidates, etdfields.docstr, etdfields.metatags, etdfields.file, etdfields.sinfo, valuetype, ikeytype, inumerictype, rngchk);
        }
        else {
            assert(false, `Unexpected token ${tok.value} when parsing IRTypedeclTypeDecl`);
        }
    }
}

class IRTypedeclCStringDecl extends IRTypedeclTypeDecl {
    readonly rechk: IRLiteralCRegexExpression | undefined;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, rngchk: {min: IRImmediateExpression | undefined, max: IRImmediateExpression | undefined} | undefined, rechk: IRLiteralCRegexExpression | undefined) {
        super(tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstr, metatags, file, sinfo, new IRNominalTypeSignature("CString"), true, false, rngchk);
        this.rechk = rechk;
    }

    override toBAPI(): string {
        const rngchkstr = this.rngchk !== undefined ? this.toBAPI_RNGCheck() : 'none';
        const rechkstr = this.rechk !== undefined ? `some(${this.rechk.toBAPI()})` : 'none';

        return `Assembly::TypedeclCStringDecl{${this.toBAPI_IRAbstractEntityTypeDecl()}, ${this.iskeytype}, ${this.isnumerictype}, ${rngchkstr}, ${rechkstr}}`;
    }

    static parseBAPIAsIRTypedeclCStringDecl(lexer: BAPILexer): IRTypedeclCStringDecl {
        lexer.consumeToken();

        const etdfields = IRAbstractEntityTypeDecl.parseBAPI_IRAbstractEntityTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol(",");
        IRTypeSignature.parseBAPI(lexer);
        lexer.ensureAndConsumeSymbol(",");
        lexer.consumeToken().kind === BAPITokenKind.TrueLiteral;
        lexer.ensureAndConsumeSymbol(",");
        lexer.consumeToken().kind === BAPITokenKind.TrueLiteral;
        lexer.ensureAndConsumeSymbol(",");
        let rngchk: {min: IRImmediateExpression | undefined, max: IRImmediateExpression | undefined} | undefined = undefined;
        if(lexer.peekTokenKind() === BAPITokenKind.NoneLiteral) {
            lexer.consumeToken();
        }
        else {
            lexer.ensureAndConsumeSymbol("some");
            lexer.ensureAndConsumeSymbol("(");
            rngchk = IRTypedeclTypeDecl.parseBAPI_RNGCheck(lexer);
            lexer.ensureAndConsumeSymbol(")");
        }
        lexer.ensureAndConsumeSymbol(",");
        let rechk: IRLiteralCRegexExpression | undefined = undefined;
        const rechktok = lexer.consumeToken();
        if(rechktok.kind !== BAPITokenKind.NoneLiteral) {
            lexer.ensureAndConsumeSymbol("(");
            rechk = IRLiteralCRegexExpression.parseBAPIAsIRLiteralCRegexExpression(lexer);
            lexer.ensureAndConsumeSymbol(")");
        }

        lexer.ensureAndConsumeSymbol("}");
        return new IRTypedeclCStringDecl(etdfields.tkey, etdfields.invariants, etdfields.validates, etdfields.saturatedProvides, etdfields.allInvariants, etdfields.allValidates, etdfields.docstr, etdfields.metatags, etdfields.file, etdfields.sinfo, rngchk, rechk);
    }
}

class IRTypedeclStringDecl extends IRTypedeclTypeDecl {
    readonly rechk: IRLiteralUnicodeRegexExpression | undefined;
    
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], saturatedProvides: IRTypeSignature[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, rngchk: {min: IRImmediateExpression | undefined, max: IRImmediateExpression | undefined} | undefined, rechk: IRLiteralUnicodeRegexExpression | undefined) {
        super(tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstr, metatags, file, sinfo, new IRNominalTypeSignature("String"), true, false, rngchk);
        this.rechk = rechk;
    }

    override toBAPI(): string {
        const rngchkstr = this.rngchk !== undefined ? this.toBAPI_RNGCheck() : 'none';
        const rechkstr = this.rechk !== undefined ? `some(${this.rechk.toBAPI()})` : 'none';
        
        return `Assembly::TypedeclStringDecl{${this.toBAPI_IRAbstractEntityTypeDecl()}, ${this.iskeytype}, ${this.isnumerictype}, ${rngchkstr}, ${rechkstr}}`;
    }

    static parseBAPIAsIRTypedeclStringDecl(lexer: BAPILexer): IRTypedeclStringDecl {
        lexer.consumeToken();

        const etdfields = IRAbstractEntityTypeDecl.parseBAPI_IRAbstractEntityTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol(",");
        IRTypeSignature.parseBAPI(lexer);
        lexer.ensureAndConsumeSymbol(",");
        lexer.consumeToken().kind === BAPITokenKind.TrueLiteral;
        lexer.ensureAndConsumeSymbol(",");
        lexer.consumeToken().kind === BAPITokenKind.TrueLiteral;
        lexer.ensureAndConsumeSymbol(",");
        let rngchk: {min: IRImmediateExpression | undefined, max: IRImmediateExpression | undefined} | undefined = undefined;
        if(lexer.peekTokenKind() === BAPITokenKind.NoneLiteral) {
            lexer.consumeToken();
        }
        else {
            lexer.ensureAndConsumeSymbol("some");
            lexer.ensureAndConsumeSymbol("(");
            rngchk = IRTypedeclTypeDecl.parseBAPI_RNGCheck(lexer);
            lexer.ensureAndConsumeSymbol(")");
        }
        lexer.ensureAndConsumeSymbol(",");
        let rechk: IRLiteralUnicodeRegexExpression | undefined = undefined;
        const rechktok = lexer.consumeToken();
        if(rechktok.kind !== BAPITokenKind.NoneLiteral) {
            lexer.ensureAndConsumeSymbol("(");
            rechk = IRLiteralUnicodeRegexExpression.parseBAPIAsIRLiteralUnicodeRegexExpression(lexer);
            lexer.ensureAndConsumeSymbol(")");
        }

        lexer.ensureAndConsumeSymbol("}");
        return new IRTypedeclStringDecl(etdfields.tkey, etdfields.invariants, etdfields.validates, etdfields.saturatedProvides, etdfields.allInvariants, etdfields.allValidates, etdfields.docstr, etdfields.metatags, etdfields.file, etdfields.sinfo, rngchk, rechk);
    }
}

//TODO: Path typedecl

abstract class IRInternalEntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, [], [], [], "std", saturatedProvides, [], [], [], docstr, metatags, file, sinfo);
    }

    toBAPI_IRInternalEntityTypeDecl(): string {
        return this.toBAPI_IRAbstractEntityTypeDecl();
    }

    static parseBAPI_IRInternalEntityTypeDecl(lexer: BAPILexer): { tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo } {
        return IRAbstractEntityTypeDecl.parseBAPI_IRAbstractEntityTypeDecl(lexer);
    }
}

class IRPrimitiveEntityTypeDecl extends IRInternalEntityTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo) {
        super(tkey, [], docstr, [], file, sinfo);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [];
    }

    override toBAPI(): string {
        return `Assembly::PrimitiveEntityTypeDecl{${this.toBAPI_IRInternalEntityTypeDecl()}}`;
    }

    static parseBAPIAsIRPrimitiveEntityTypeDecl(lexer: BAPILexer): IRPrimitiveEntityTypeDecl {
        lexer.consumeToken(); //Assembly::PrimitiveEntityTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRInternalEntityTypeDecl.parseBAPI_IRInternalEntityTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IRPrimitiveEntityTypeDecl(etdfields.tkey, etdfields.docstr, etdfields.file, etdfields.sinfo);
    }
}

abstract class IRConstructableTypeDecl extends IRInternalEntityTypeDecl {
    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo) {
        super(tkey, saturatedProvides, docstr, [], file, sinfo);
    }

    toBAPI_IRConstructableTypeDecl(): string {
        return this.toBAPI_IRAbstractEntityTypeDecl();
    }

    static parseBAPI_IRConstructableTypeDecl(lexer: BAPILexer): { tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo } {
        return IRInternalEntityTypeDecl.parseBAPI_IRInternalEntityTypeDecl(lexer);
    }
}

class IROkTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    override toBAPI(): string {
        assert(false, "IROkTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIROkTypeDecl(lexer: BAPILexer): IROkTypeDecl {
        assert(false, "IROkTypeDecl.parseBAPI_IROkTypeDecl() is not implemented yet");
    }
}

class IRFailTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    override toBAPI(): string {
        assert(false, "IRFailTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRFailTypeDecl(lexer: BAPILexer): IRFailTypeDecl {
        assert(false, "IRFailTypeDecl.parseBAPI_IRFailTypeDecl() is not implemented yet");
    }
}

class IRAPIErrorTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    override toBAPI(): string {
        assert(false, "IRAPIErrorTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRAPIErrorTypeDecl(lexer: BAPILexer): IRAPIErrorTypeDecl {
        assert(false, "IRAPIErrorTypeDecl.parseBAPI_IRAPIErrorTypeDecl() is not implemented yet");
    }
}

class IRAPIRejectedTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    override toBAPI(): string {
        assert(false, "IRAPIRejectedTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRAPIRejectedTypeDecl(lexer: BAPILexer): IRAPIRejectedTypeDecl {
        assert(false, "IRAPIRejectedTypeDecl.parseBAPI_IRAPIRejectedTypeDecl() is not implemented yet");
    }
}

class IRAPIDeniedTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    override toBAPI(): string {
        assert(false, "IRAPIDeniedTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRAPIDeniedTypeDecl(lexer: BAPILexer): IRAPIDeniedTypeDecl {
        assert(false, "IRAPIDeniedTypeDecl.parseBAPI_IRAPIDeniedTypeDecl() is not implemented yet");
    }
}

class IRAPIFlaggedTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    override toBAPI(): string {
        assert(false, "IRAPIFlaggedTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRAPIFlaggedTypeDecl(lexer: BAPILexer): IRAPIFlaggedTypeDecl {
        assert(false, "IRAPIFlaggedTypeDecl.parseBAPI_IRAPIFlaggedTypeDecl() is not implemented yet");
    }
}

class IRAPISuccessTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype];
    }

    override toBAPI(): string {
        assert(false, "IRAPISuccessTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRAPISuccessTypeDecl(lexer: BAPILexer): IRAPISuccessTypeDecl {
        assert(false, "IRAPISuccessTypeDecl.parseBAPI_IRAPISuccessTypeDecl() is not implemented yet");
    }
}

class IRSomeTypeDecl extends IRConstructableTypeDecl {
    readonly ttype: IRTypeSignature;

    constructor(tkey: string, saturatedProvides: IRTypeSignature[], docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature) {
        super(tkey, saturatedProvides, docstr, file, sinfo);
        this.ttype = ttype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype];
    }

    override toBAPI(): string {
        assert(false, "IRSomeTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRSomeTypeDecl(lexer: BAPILexer): IRSomeTypeDecl {
        assert(false, "IRSomeTypeDecl.parseBAPI_IRSomeTypeDecl() is not implemented yet");
    }
}

class IRMapEntryTypeDecl extends IRConstructableTypeDecl {
    readonly ktype: IRTypeSignature;
    readonly vtype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ktype: IRTypeSignature, vtype: IRTypeSignature) {
        super(tkey, [], docstr, file, sinfo);
        this.ktype = ktype;
        this.vtype = vtype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ktype, this.vtype];
    }

    override toBAPI(): string {
        assert(false, "IRMapEntryTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRMapEntryTypeDecl(lexer: BAPILexer): IRMapEntryTypeDecl {
        assert(false, "IRMapEntryTypeDecl.parseBAPI_IRMapEntryTypeDecl() is not implemented yet");
    }
}

abstract class IRAbstractCollectionTypeDecl extends IRInternalEntityTypeDecl {
    readonly oftype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, [], docstr, [], file, sinfo);
        this.oftype = oftype;
    }

    toBAPI_IRAbstractCollectionTypeDecl(): string {
        return this.toBAPI_IRInternalEntityTypeDecl() + ", " + this.oftype.toBAPI();
    }

    static parseBAPI_IRAbstractCollectionTypeDecl(lexer: BAPILexer): { tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature } {
        const etdfields = IRInternalEntityTypeDecl.parseBAPI_IRInternalEntityTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol(",");
        const oftype = IRTypeSignature.parseBAPI(lexer);

        return {...etdfields, oftype: oftype};
    }
}

class IRListTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.oftype];
    }

    override toBAPI(): string {
        return `Assembly::ListTypeDecl{${this.toBAPI_IRAbstractCollectionTypeDecl()}}`;
    }

    static parseBAPIAsIRListTypeDecl(lexer: BAPILexer): IRListTypeDecl {
        lexer.consumeToken(); //Assembly::IRListTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractCollectionTypeDecl.parseBAPI_IRAbstractCollectionTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IRListTypeDecl(etdfields.tkey, etdfields.docstr, etdfields.file, etdfields.sinfo, etdfields.oftype);
    }
}

class IRStackTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.oftype];
    }

    override toBAPI(): string {
        return `Assembly::StackTypeDecl{${this.toBAPI_IRAbstractCollectionTypeDecl()}}`;
    }

    static parseBAPIAsIRStackTypeDecl(lexer: BAPILexer): IRStackTypeDecl {
        lexer.consumeToken(); //Assembly::IRStackTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractCollectionTypeDecl.parseBAPI_IRAbstractCollectionTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IRStackTypeDecl(etdfields.tkey, etdfields.docstr, etdfields.file, etdfields.sinfo, etdfields.oftype);
    }
}

class IRQueueTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.oftype];
    }
    override toBAPI(): string {
        return `Assembly::QueueTypeDecl{${this.toBAPI_IRAbstractCollectionTypeDecl()}}`;
    }

    static parseBAPIAsIRQueueTypeDecl(lexer: BAPILexer): IRQueueTypeDecl {
        lexer.consumeToken(); //Assembly::IRQueueTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractCollectionTypeDecl.parseBAPI_IRAbstractCollectionTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IRQueueTypeDecl(etdfields.tkey, etdfields.docstr, etdfields.file, etdfields.sinfo, etdfields.oftype);
    }
}

class IRSetTypeDecl extends IRAbstractCollectionTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.oftype];
    }

    override toBAPI(): string {
        return `Assembly::SetTypeDecl{${this.toBAPI_IRAbstractCollectionTypeDecl()}}`;
    }

    static parseBAPIAsIRSetTypeDecl(lexer: BAPILexer): IRSetTypeDecl {
        lexer.consumeToken(); //Assembly::IRSetTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractCollectionTypeDecl.parseBAPI_IRAbstractCollectionTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IRSetTypeDecl(etdfields.tkey, etdfields.docstr, etdfields.file, etdfields.sinfo, etdfields.oftype);
    }
}

class IRMapTypeDecl extends IRAbstractCollectionTypeDecl {
    readonly ktype: IRTypeSignature;
    readonly vtype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, oftype: IRTypeSignature, ktype: IRTypeSignature, vtype: IRTypeSignature) {
        super(tkey, docstr, file, sinfo, oftype);
        this.ktype = ktype;
        this.vtype = vtype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
       return [this.oftype, this.ktype, this.vtype];
    }

    override toBAPI(): string {
        return `Assembly::MapTypeDecl{${this.toBAPI_IRAbstractCollectionTypeDecl()}, ${this.ktype.toBAPI()}, ${this.vtype.toBAPI()}}`;
    }

    static parseBAPIAsIRMapTypeDecl(lexer: BAPILexer): IRMapTypeDecl {
        lexer.consumeToken(); //Assembly::MapTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractCollectionTypeDecl.parseBAPI_IRAbstractCollectionTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol(",");
        const ktype = IRTypeSignature.parseBAPI(lexer);
        lexer.ensureAndConsumeSymbol(",");
        const vtype = IRTypeSignature.parseBAPI(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IRMapTypeDecl(etdfields.tkey, etdfields.docstr, etdfields.file, etdfields.sinfo, etdfields.oftype, ktype, vtype);
    }
}

class IREventListTypeDecl extends IRInternalEntityTypeDecl {
    readonly etype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, etype: IRTypeSignature) {
        super(tkey, [], docstr, [], file, sinfo);
        this.etype = etype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.etype];
    }

    override toBAPI(): string {
        assert(false, "IREventListTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIREventListTypeDecl(lexer: BAPILexer): IREventListTypeDecl {
        assert(false, "IREventListTypeDecl.parseBAPI_IREventListTypeDecl() is not implemented yet");
    }
}

class IREntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        const ffdecls = this.saturatedBFieldInfo.map((bf) => {
            const ctt = alltypes.get(bf.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
            const bfdecl = ctt.fields.find(f => f.fkey === bf.fkey) as IRMemberFieldDecl;
            return bfdecl.declaredType;
        });

        return ffdecls;
    }

    override toBAPI(): string {
        return `Assembly::EntityTypeDecl{${this.toBAPI_IRAbstractEntityTypeDecl()}}`;
    }

    static parseBAPIAsIREntityTypeDecl(lexer: BAPILexer): IREntityTypeDecl {
        lexer.consumeToken(); //Assembly::EntityTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractEntityTypeDecl.parseBAPI_IRAbstractEntityTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IREntityTypeDecl(etdfields.tkey, etdfields.invariants, etdfields.validates, etdfields.fields, etdfields.etag, etdfields.saturatedProvides, etdfields.saturatedBFieldInfo, etdfields.allInvariants, etdfields.allValidates, etdfields.docstr, etdfields.metatags, etdfields.file, etdfields.sinfo);
    }
}

abstract class IRAbstractConceptTypeDecl extends IRAbstractNominalTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, "std", saturatedProvides, saturatedBFieldInfo, [], [], docstr, metatags, file, sinfo);
    }

    toBAPI_IRAbstractConceptTypeDecl(): string {
        return this.toBAPI_IRAbstractNominalTypeDecl();
    }

    static parseBAPI_IRAbstractConceptTypeDecl(lexer: BAPILexer): { tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo } {
        return IRAbstractNominalTypeDecl.parseBAPI_IRAbstractNominalTypeDecl(lexer);
    }
}

abstract class IRInternalConceptTypeDecl extends IRAbstractConceptTypeDecl {
    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, [], [], [], [], [], docstr, metatags, file, sinfo);
    }

    toBAPI_IRInternalConceptTypeDecl(): string {
        return this.toBAPI_IRAbstractConceptTypeDecl();
    }

    static parseBAPI_IRInternalConceptTypeDecl(lexer: BAPILexer): { tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo } {
        return IRAbstractConceptTypeDecl.parseBAPI_IRAbstractConceptTypeDecl(lexer);
    }
}

class IROptionTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, sometype: IRTypeSignature) {
        super(tkey, docstr, [], file, sinfo);
        this.ttype = ttype;
        this.sometype = sometype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.sometype];
    }

    override toBAPI(): string {
        assert(false, "IROptionTypeDecl.toBAPI() is not implemented yet");
    }
    
    static parseBAPIAsIROptionTypeDecl(lexer: BAPILexer): IROptionTypeDecl {
        assert(false, "IROptionTypeDecl.parseBAPI_IROptionTypeDecl() is not implemented yet");
    }
}

class IRResultTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    readonly oktype: IRTypeSignature;
    readonly failtype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature, oktype: IRTypeSignature, failtype: IRTypeSignature) {
        super(tkey, docstr, [], file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
        this.oktype = oktype;
        this.failtype = failtype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype, this.oktype, this.failtype];
    }

    override toBAPI(): string {
        assert(false, "IRResultTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRResultTypeDecl(lexer: BAPILexer): IRResultTypeDecl {
        assert(false, "IRResultTypeDecl.parseBAPI_IRResultTypeDecl() is not implemented yet");
    }
}

class IRAPIResultTypeDecl extends IRInternalConceptTypeDecl {
    readonly ttype: IRTypeSignature;
    readonly etype: IRTypeSignature;

    readonly errortype: IRTypeSignature;
    readonly rejectedtype: IRTypeSignature;
    readonly deniedtype: IRTypeSignature;
    readonly flaggedtype: IRTypeSignature;
    readonly successtype: IRTypeSignature;

    constructor(tkey: string, docstr: IRDeclarationDocString | undefined, file: string, sinfo: IRSourceInfo, ttype: IRTypeSignature, etype: IRTypeSignature, errortype: IRTypeSignature, rejectedtype: IRTypeSignature, deniedtype: IRTypeSignature, flaggedtype: IRTypeSignature, successtype: IRTypeSignature) {
        super(tkey, docstr, [], file, sinfo);
        this.ttype = ttype;
        this.etype = etype;
        this.errortype = errortype;
        this.rejectedtype = rejectedtype;
        this.deniedtype = deniedtype;
        this.flaggedtype = flaggedtype;
        this.successtype = successtype;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        return [this.ttype, this.etype, this.errortype, this.rejectedtype, this.deniedtype, this.flaggedtype, this.successtype];
    }

    override toBAPI(): string {
        assert(false, "IRAPIResultTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRAPIResultTypeDecl(lexer: BAPILexer): IRAPIResultTypeDecl {
        assert(false, "IRAPIResultTypeDecl.parseBAPI_IRAPIResultTypeDecl() is not implemented yet");
    }
}

class IRConceptTypeDecl extends IRAbstractConceptTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, saturatedProvides, saturatedBFieldInfo, docstr, metatags, file, sinfo);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        const ffdecls = this.saturatedBFieldInfo.map(bf => {
            const ctt = alltypes.get(bf.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
            const bfdecl = ctt.fields.find(f => f.fkey === bf.fkey) as IRMemberFieldDecl;
            return bfdecl.declaredType;
        });

        return [new IRNominalTypeSignature(this.tkey), ...ffdecls];
    }

    override toBAPI(): string {
        return `Assembly::ConceptTypeDecl{${this.toBAPI_IRAbstractConceptTypeDecl()}}`;
    }

    static parseBAPIAsIRConceptTypeDecl(lexer: BAPILexer): IRConceptTypeDecl {
        lexer.consumeToken(); //Assembly::ConceptTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractConceptTypeDecl.parseBAPI_IRAbstractConceptTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IRConceptTypeDecl(etdfields.tkey, etdfields.invariants, etdfields.validates, etdfields.fields, etdfields.saturatedProvides, etdfields.saturatedBFieldInfo, etdfields.docstr, etdfields.metatags, etdfields.file, etdfields.sinfo);
    }
}

class IRDatatypeMemberEntityTypeDecl extends IRAbstractEntityTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], etag: "std" | "status" | "event", saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        super(tkey, invariants, validates, fields, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags, file, sinfo);
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        const ffdecls = this.saturatedBFieldInfo.map(bf => {
            const ctt = alltypes.get(bf.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
            const bfdecl = ctt.fields.find(f => f.fkey === bf.fkey) as IRMemberFieldDecl;
            return bfdecl.declaredType;
        });

        return ffdecls;
    }

    override toBAPI(): string {
        return `Assembly::DatatypeMemberEntityTypeDecl{${this.toBAPI_IRAbstractEntityTypeDecl()}}`;
    }

    static parseBAPIAsIRDatatypeMemberEntityTypeDecl(lexer: BAPILexer): IRDatatypeMemberEntityTypeDecl {
        lexer.consumeToken(); //Assembly::DatatypeMemberEntityTypeDecl
        lexer.ensureAndConsumeSymbol("{");
        const etdfields = IRAbstractEntityTypeDecl.parseBAPI_IRAbstractEntityTypeDecl(lexer);
        lexer.ensureAndConsumeSymbol("}");

        return new IRDatatypeMemberEntityTypeDecl(etdfields.tkey, etdfields.invariants, etdfields.validates, etdfields.fields, etdfields.etag, etdfields.saturatedProvides, etdfields.saturatedBFieldInfo, etdfields.allInvariants, etdfields.allValidates, etdfields.docstr, etdfields.metatags, etdfields.file, etdfields.sinfo);
    }
}

class IRDatatypeTypeDecl extends IRAbstractConceptTypeDecl {
    readonly dataelems: IRTypeSignature[];

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], fields: IRMemberFieldDecl[], saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string, fname: string, ftype: IRTypeSignature }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, dataelems: IRTypeSignature[]) {
        super(tkey, invariants, validates, fields, saturatedProvides, saturatedBFieldInfo, docstr, metatags, file, sinfo);
        this.dataelems = dataelems;
    }

    override getDeclDependencyTypes(alltypes: Map<string, IRAbstractNominalTypeDecl>): IRTypeSignature[] {
        const ffdecls = this.saturatedBFieldInfo.map(bf => {
            const ctt = alltypes.get(bf.containingtype.tkeystr) as IRAbstractNominalTypeDecl;
            const bfdecl = ctt.fields.find(f => f.fkey === bf.fkey) as IRMemberFieldDecl;
            return bfdecl.declaredType;
        });
        
        return [new IRNominalTypeSignature(this.tkey), ...ffdecls];
    }

    override toBAPI(): string {
        assert(false, "IRDatatypeTypeDecl.toBAPI() is not implemented yet");
    }

    static parseBAPIAsIRDatatypeTypeDecl(lexer: BAPILexer): IRDatatypeTypeDecl {
        assert(false, "IRDatatypeTypeDecl.parseBAPI_IRDatatypeTypeDecl() is not implemented yet");
    }
}

class IREnvironmentVariableInformation {
    readonly evname: string; //identifier or cstring
    readonly evtype: IRTypeSignature;
    readonly required: boolean;
    readonly optdefault: { stmts: IRStatement[], value: IRSimpleExpression } | undefined;

    constructor(evname: string, evtype: IRTypeSignature, required: boolean, optdefault: { stmts: IRStatement[], value: IRSimpleExpression } | undefined) {
        this.evname = evname;
        this.evtype = evtype;
        this.required = required;
        this.optdefault = optdefault;
    }
}

class IRResourceInformation {
    //TODO: fill this in
}

class IRTaskConfiguration {
    timeout: number | undefined;
    retry: {delay: number, tries: number} | undefined;
    priority: "immediate" | "fast" | "normal" | "longrunning" | "background" | "optional" | undefined;

    constructor(timeout: number | undefined, retry: {delay: number, tries: number} | undefined, priority: "immediate" | "fast" | "normal" | "longrunning" | "background" | "optional" | undefined) {
        this.timeout = timeout;
        this.retry = retry;
        this.priority = priority;
    }
}

class IRAPIDecl {
    readonly ikey: string;

    readonly params: IRInvokeParameterDecl[];    
    readonly resultType: IRTypeSignature;
    readonly eventType: IRTypeSignature | undefined;

    readonly preconditions: IRPreConditionDecl[];
    readonly postconditions: IRPostConditionDecl[];

    readonly configs: IRTaskConfiguration;

    readonly statusinfo: IRTypeSignature[];
    readonly envreqs: IREnvironmentVariableInformation[];
    readonly resourcereqs: IRResourceInformation;

    readonly body: IRBody;

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(ikey: string, params: IRInvokeParameterDecl[], resultType: IRTypeSignature, eventType: IRTypeSignature | undefined, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, body: IRBody, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        this.ikey = ikey;
        this.params = params;
        this.resultType = resultType;
        this.eventType = eventType;
        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.configs = configs;
        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;
        this.body = body;
        this.docstr = docstr;
        this.metatags = metatags;
        this.file = file;
        this.sinfo = sinfo;
    }
}

class IRAgentDecl {
    readonly ikey: string;

    readonly params: IRInvokeParameterDecl[];    
    readonly resultType: IRTypeSignature | undefined; //This may be set on a per call-site basis
    readonly eventType: IRTypeSignature | undefined;

    readonly preconditions: IRPreConditionDecl[];
    readonly postconditions: IRPostConditionDecl[];

    readonly configs: IRTaskConfiguration;

    readonly statusinfo: IRTypeSignature[];
    readonly envreqs: IREnvironmentVariableInformation[];
    readonly resourcereqs: IRResourceInformation;

    readonly body: IRBody;

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    constructor(ikey: string, params: IRInvokeParameterDecl[], resultType: IRTypeSignature | undefined, eventType: IRTypeSignature | undefined, preconditions: IRPreConditionDecl[], postconditions: IRPostConditionDecl[], configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, body: IRBody, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo) {
        this.ikey = ikey;
        this.params = params;
        this.resultType = resultType;
        this.eventType = eventType;
        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.configs = configs;
        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;
        this.body = body;
        this.docstr = docstr;
        this.metatags = metatags;
        this.file = file;
        this.sinfo = sinfo;
    }
}

class IRTaskDecl {
    readonly tkey: string;

    readonly invariants: IRInvariantDecl[];
    readonly fields: IRMemberFieldDecl[];

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    readonly file: string;
    readonly sinfo: IRSourceInfo;

    readonly configs: IRTaskConfiguration;

    readonly statusinfo: IRTypeSignature[];
    readonly envreqs: IREnvironmentVariableInformation[];
    readonly resourcereqs: IRResourceInformation;
    readonly eventinfo: IRTypeSignature[];

    readonly imain: string; //invoke key of main task action
    readonly icleanup: {
        onterminate: string | undefined //invoke key of on-terminate action -- when we have a cancel/timeout/or parent abort that we cooperatively check and we are graceful in cleanup
        onerror: string | undefined //invoke key of on-error action -- when we abort from a runtime failure and we are bailing
        ondrop: string | undefined //invoke key of on-drop action -- when we have completed but our result is unused and we gracefully clean up
    };

    constructor(tkey: string, invariants: IRInvariantDecl[], fields: IRMemberFieldDecl[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[], file: string, sinfo: IRSourceInfo, configs: IRTaskConfiguration, statusinfo: IRTypeSignature[], envreqs: IREnvironmentVariableInformation[], resourcereqs: IRResourceInformation, eventinfo: IRTypeSignature[], imain: string, icleanup: { onterminate: string | undefined; onerror: string | undefined; ondrop: string | undefined; }) {
        this.tkey = tkey;
        this.invariants = invariants;
        this.fields = fields;
        this.docstr = docstr;
        this.metatags = metatags;
        this.file = file;
        this.sinfo = sinfo;
        
        this.configs = configs;
        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;
        this.eventinfo = eventinfo;

        this.imain = imain;
        this.icleanup = icleanup;
    }
}

class IRLambdaParameterPackDecl {
    readonly tkeystr: string;
    readonly invtrgt: string;
    readonly stdvalues: {vname: string, vtype: IRTypeSignature}[];
    readonly lambdavalues: {lname: string, ltypekey: string}[];

    constructor(tkeystr: string, invtrgt: string, stdvalues: {vname: string, vtype: IRTypeSignature}[], lambdavalues: {lname: string, ltypekey: string}[]) {
        this.tkeystr = tkeystr;
        this.invtrgt = invtrgt;
        this.stdvalues = stdvalues;
        this.lambdavalues = lambdavalues;
    }
}

class IRAssembly {
    readonly cregexps: IRCRegex[] = [];
    readonly uregexps: IRURegex[] = [];

    readonly constants: IRConstantDecl[] = [];

    readonly tests: IRTestDecl[] = [];
    readonly examples: IRExampleDecl[] = [];

    readonly invokes: IRInvokeDecl[] = [];
    readonly taskactions: IRTaskActionDecl[] = [];

    readonly primitives: IRPrimitiveEntityTypeDecl[] = [];
    readonly constructables: IRConstructableTypeDecl[] = [];
    readonly collections: IRAbstractCollectionTypeDecl[] = [];
    readonly eventlists: IREventListTypeDecl[] = [];

    readonly enums: IREnumTypeDecl[] = [];
    readonly typedecls: IRTypedeclTypeDecl[] = [];
    readonly cstringoftypedecls: IRTypedeclCStringDecl[] = [];
    readonly stringoftypedecls: IRTypedeclStringDecl[] = [];

    readonly entities: IREntityTypeDecl[] = [];
    readonly datamembers: IRDatatypeMemberEntityTypeDecl[] = [];

    readonly pconcepts: IRInternalConceptTypeDecl[] = [];
    readonly concepts: IRConceptTypeDecl[] = [];
    readonly datatypes: IRDatatypeTypeDecl[] = [];

    readonly apis: IRAPIDecl[] = [];
    readonly agents: IRAgentDecl[] = [];
    readonly tasks: IRTaskDecl[] = [];

    readonly alltypes: Map<string, IRAbstractNominalTypeDecl> = new Map<string, IRAbstractNominalTypeDecl>();
    readonly allinvokes: Map<string, IRInvokeMetaDecl> = new Map<string, IRInvokeMetaDecl>();
    readonly alllambdas: Map<string, IRLambdaParameterPackDecl> = new Map<string, IRLambdaParameterPackDecl>();

    readonly elists: IREListTypeSignature[] = [];
    readonly dashtypes: IRDashResultTypeSignature[] = [];
    readonly formats: IRFormatTypeSignature[] = [];
    readonly lpacksigs: IRLambdaParameterPackTypeSignature[] = [];

    readonly formatcstrings: IRLiteralFormatCStringExpression[] = [];
    readonly formatstrings: IRLiteralFormatStringExpression[] = [];

    readonly concretesubtypes: Map<string, IRTypeSignature[]> = new Map<string, IRTypeSignature[]>();
    readonly concretesupertypes: Map<string, IRTypeSignature[]> = new Map<string, IRTypeSignature[]>();

    readonly typedeporder: IRTypeSignature[] = [];
    readonly typedepcycles: IRTypeSignature[][] = [];

    maxerrorid: number = 0;

    constructor() {
    }

    computeSubtypeInfo() {
        const alltl = [...this.alltypes.values()];

        for(let i = 0; i < alltl.length; i++) {
            const ctt = alltl[i];

            if(ctt instanceof IRAbstractConceptTypeDecl) {
                if(!this.concretesubtypes.has(ctt.tkey)) {
                    this.concretesubtypes.set(ctt.tkey, []);
                }
            }
            else {
                if(!this.concretesupertypes.has(ctt.tkey)) {
                    this.concretesupertypes.set(ctt.tkey, []);
                }
                let superl = this.concretesupertypes.get(ctt.tkey) as IRTypeSignature[];

                const cctsig = new IRNominalTypeSignature(ctt.tkey);
                for(let j = 0; j < ctt.saturatedProvides.length; j++) {
                    const ssuper = ctt.saturatedProvides[j];

                    if(!this.concretesubtypes.has(ssuper.tkeystr)) {
                        this.concretesubtypes.set(ssuper.tkeystr, []);
                    }
                    (this.concretesubtypes.get(ssuper.tkeystr) as IRTypeSignature[]).push(cctsig);
                    superl.push(ssuper);
                }
            }
        }

        for(const csubts of this.concretesubtypes.values()) {
            csubts.sort((a, b) => a.tkeystr.localeCompare(b.tkeystr));   
        }

        for(const csupts of this.concretesupertypes.values()) {
            csupts.sort((a, b) => a.tkeystr.localeCompare(b.tkeystr));   
        }
    }

    private getTypeDependencyInfo(tsig: IRTypeSignature): IRTypeSignature[] {
        let ttl: IRTypeSignature[] = [];
        if(tsig instanceof IRLambdaParameterPackTypeSignature) {
            const lsdecl = this.alllambdas.get(tsig.tkeystr) as IRLambdaParameterPackDecl;
            ttl = [
                ...lsdecl.stdvalues.map((sv) => sv.vtype),
                ...lsdecl.lambdavalues.map((lv) => new IRLambdaParameterPackTypeSignature(lv.ltypekey))
            ];
        }
        else if(tsig instanceof IRNominalTypeSignature) {
            const ttdecl = this.alltypes.get(tsig.tkeystr) as IRAbstractNominalTypeDecl;
            ttl = ttdecl.getDeclDependencyTypes(this.alltypes);
        }
        else {
            ttl = tsig.getDirectDependencyTypes();            
        }

        //now make all the concrete subtypes explicit
        let allttl: IRTypeSignature[] = [];
        for(let i = 0; i < ttl.length; i++) {
            allttl.push(ttl[i]);

            const csubts = this.concretesubtypes.get(ttl[i].tkeystr);
            if(csubts !== undefined) {
                for(let j = 0; j < csubts.length; j++) {
                    allttl.push(csubts[j]);
                }
            }
        }

        //now make the result unique
        let resl: IRTypeSignature[] = [];
        for(let i = 0; i < allttl.length; i++) {
            if(resl.findIndex((t) => t.tkeystr === allttl[i].tkeystr) === -1) {
                resl.push(allttl[i]);
            }
        }

        return resl;
    }

    private visitType(tsig: IRTypeSignature, visited: Set<string>) {
        if(visited.has(tsig.tkeystr)) {
            return;
        }

        //If this is a SCC then we don't revisit this and we need to handle the cycle elsewhere
        visited.add(tsig.tkeystr);

        const deps = this.getTypeDependencyInfo(tsig);
        for(let i = 0; i < deps.length; i++) {
            this.visitType(deps[i], visited);
        }

        this.typedeporder.push(tsig);
    }

    private computeAllTypes(): IRTypeSignature[] {
        const allndecls = [...this.alltypes.values()].map(td => new IRNominalTypeSignature(td.tkey));
        const allsdtypes = [...this.elists, ...this.dashtypes, ...this.formats, ...this.lpacksigs];

        return [...allndecls, ...allsdtypes];
    }

    private getTypesCount(visited: Set<string>): [IRTypeSignature, number][] {
        const allpending = this.computeAllTypes().filter((t) => !visited.has(t.tkeystr));
        const ttcount = new Map<string, number>();

        for(let i = 0; i < allpending.length; i++) {
            ttcount.set(allpending[i].tkeystr, 0);
        }

        for(let i = 0; i < allpending.length; i++) {
            const deps = this.getTypeDependencyInfo(allpending[i]);
            for(let j = 0; j < deps.length; j++) {
                if(allpending[i].tkeystr !== deps[j].tkeystr) {
                    const ccount = ttcount.get(deps[j].tkeystr) as number;
                    ttcount.set(deps[j].tkeystr, ccount + 1);
                }
            }
        }

        return allpending.map<[IRTypeSignature, number]>((t) => [t, ttcount.get(t.tkeystr) as number]).sort((a, b) => a[1] - b[1]);
    }

    computeTypeDependencyInfo() {
        const visited = new Set<string>();
        let toproc = this.getTypesCount(visited);

        while(toproc.length !== 0) {
            const nrval = toproc.shift() as [IRTypeSignature, number];
            this.visitType(nrval[0], visited);

            if(nrval[1] !== 0) {
                toproc = this.getTypesCount(visited);
            }
        }

        let orderedtypes = [...this.typedeporder];
        while(orderedtypes.length !== 0) {
            const ctt = orderedtypes[0];
            const deps = this.getTypeDependencyInfo(ctt);

            let scc: IRTypeSignature[] = [];
            let cycdeps = deps.filter((d) => orderedtypes.findIndex((t) => t.tkeystr === d.tkeystr) !== -1);
            if(cycdeps.length !== 0) {
                let foundmore = true;
                while(foundmore) {
                    foundmore = false;
                    const olen = cycdeps.length;
                    for(let i = 0; i < olen; ++i) {
                        const ndeps = this.getTypeDependencyInfo(cycdeps[i]);
                        for(let j = 0; j < ndeps.length; ++j) {
                            let orr = orderedtypes.findIndex((t) => t.tkeystr === ndeps[j].tkeystr) !== -1;
                            let nadd = cycdeps.findIndex((t) => t.tkeystr === ndeps[j].tkeystr) === -1;
                            if(orr && nadd) {
                                cycdeps.push(ndeps[j])
                                foundmore = true;
                            }
                        }
                    }
                }

                scc.sort((a, b) => {
                    const apos = orderedtypes.findIndex((t) => t.tkeystr === a.tkeystr);
                    const bpos = orderedtypes.findIndex((t) => t.tkeystr === b.tkeystr);

                    return apos - bpos;
                });

                scc.push(...cycdeps);
            }

            if(scc.length === 0) {
                orderedtypes.shift();
            }
            else {
                orderedtypes = orderedtypes.filter((t) => !scc.find((st) => st.tkeystr === t.tkeystr));
                this.typedepcycles.push(scc);
            }
        }
    }

    toBAPI(): string {
        const stuff = [
            //this.cregexps.map((cr) => cr.toBAPI()),
            //this.uregexps.map((ur) => ur.toBAPI()),
            
            //this.constants.map((c) => c.toBAPI()).join(","),
            
            //this.tests.map((t) => t.toBAPI()).join(","),
            //this.examples.map((e) => e.toBAPI()).join(","),
            
            //this.invokes.map((i) => i.toBAPI()).join(","),
            //this.taskactions.map((ta) => ta.toBAPI()).join(","),
            
            ('List<Assembly::PrimitiveEntityTypeDecl>{\n        ' + this.primitives.map((p) => p.toBAPI()).join(",\n        ") + '\n    }'),
            //this.constructables.map((c) => c.toBAPI()).join(","),
            //this.collections.map((c) => c.toBAPI()).join(","),
            //this.eventlists.map((el) => el.toBAPI()).join(","),

            ('List<Assembly::EnumTypeDecl>{\n        ' + this.enums.map((e) => e.toBAPI()).join(",\n        ") + '\n    }'),
            
            ('List<Assembly::SimpleTypeDecl>{\n        ' + this.typedecls.filter((td) => td.rngchk === undefined).map((td) => td.toBAPI()).join(",\n        ") + '\n    }'),
            ('List<Assembly::BoundedTypeDecl>{\n        ' + this.typedecls.filter((td) => td.rngchk !== undefined).map((td) => td.toBAPI()).join(",\n        ") + '\n    }'),
            ('List<Assembly::CStringTypeDecl>{\n        ' + this.cstringoftypedecls.map((td) => td.toBAPI()).join(",\n        ") + '\n    }'),
            ('List<Assembly::StringTypeDecl>{\n        ' + this.stringoftypedecls.map((td) => td.toBAPI()).join(",\n        ") + '\n    }'),
            
            //this.entities.map((e) => e.toBAPI()).join(","),
            //this.datamembers.map((dm) => dm.toBAPI()).join(","),
            //this.pconcepts.map((pc) => pc.toBAPI()).join(","),
            //this.concepts.map((c) => c.toBAPI()).join(","),
            //this.datatypes.map((dt) => dt.toBAPI()).join(","),
            
            //this.apis.map((api) => api.toBAPI()).join(","),
            //this.agents.map((ag) => ag.toBAPI()).join(","),
            //this.tasks.map((t) => t.toBAPI()).join(",")

            ('Map<Assembly::TypeKey, Assembly::AbstractNominalTypeDecl>{\n        ' + Array.from(this.alltypes.entries()).map(([k, v]) => `${emitTypeKey(k)} => ${v.toBAPI()}`).join(",\n        ") + '\n    }'),
            //readonly allinvokes: Map<string, IRInvokeMetaDecl> = new Map<string, IRInvokeMetaDecl>();
            //readonly alllambdas: Map<string, IRLambdaParameterPackDecl> = new Map<string, IRLambdaParameterPackDecl>();

            ('List<Assembly::EListTypeSignature>{\n        ' + this.elists.map((el) => el.toBAPI()).join(",\n        ") + '\n    }'),
            //this.dashtypes.map((dt) => dt.toBAPI()).join(","),
            //this.formats.map((f) => f.toBAPI()).join(","),
            //this.lpacksigs.map((lp) => lp.toBAPI()).join(","),
            
            //this.formatcstrings.map((fc) => fc.toBAPI()).join(","),
            //this.formatstrings.map((fs) => fs.toBAPI()).join(","),

            //this.concretesubtypes.entries().map(([k, v]) => `Assembly::ConcreteSubtypes{${k}, [${v.map((t) => t.toBAPI()).join(",")}]}`).join(","),
            //this.concretesupertypes.entries().map(([k, v]) => `Assembly::ConcreteSupertypes{${k}, [${v.map((t) => t.toBAPI()).join(",")}]}`).join(","),

            //this.typedeporder.map((t) => `Assembly::TypeDependencyOrder{${t.toBAPI()}}`).join(","),
            //this.typedepcycles.map((c) => `Assembly::TypeDependencyCycle{[${c.map((t) => t.toBAPI()).join(",")}]} `).join(",")
        ];

        return `Assembly::Assembly{\n    ${stuff.join(",\n    ")}\n}\n`;
    }

    static parseBAPI(lexer: BAPILexer): IRAssembly {
        const tok = lexer.peekToken();
        if(tok.kind !== BAPITokenKind.TypeIdentifier || tok.value !== "Assembly::Assembly") {
            throw new Error(`Unexpected token ${tok.value} when parsing IRAssembly`);
        }

        let irasm = new IRAssembly();
        lexer.consumeToken(); //Assembly::Assembly
        lexer.ensureAndConsumeSymbol("{");

        lexer.ensureAndConsumeSymbol("List<Assembly::PrimitiveEntityTypeDecl>");
        irasm.primitives.push(...parseListOf<IRPrimitiveEntityTypeDecl>(lexer, '{', '}', ',', IRPrimitiveEntityTypeDecl.parseBAPIAsIRPrimitiveEntityTypeDecl));

        lexer.ensureAndConsumeSymbol("List<Assembly::EnumTypeDecl>");
        irasm.enums.push(...parseListOf<IREnumTypeDecl>(lexer, '{', '}', ',', IREnumTypeDecl.parseBAPIAsIREnumTypeDecl));

        lexer.ensureAndConsumeSymbol("List<Assembly::SimpleTypeDecl>");
        irasm.typedecls.push(...parseListOf<IRTypedeclTypeDecl>(lexer, '{', '}', ',', IRTypedeclTypeDecl.parseBAPIAsIRTypedeclTypeDecl));

        lexer.ensureAndConsumeSymbol("List<Assembly::BoundedTypeDecl>");
        irasm.typedecls.push(...parseListOf<IRTypedeclTypeDecl>(lexer, '{', '}', ',', IRTypedeclTypeDecl.parseBAPIAsIRTypedeclTypeDecl));

        lexer.ensureAndConsumeSymbol("List<Assembly::CStringTypeDecl>");
        irasm.cstringoftypedecls.push(...parseListOf<IRTypedeclCStringDecl>(lexer, '{', '}', ',', IRTypedeclCStringDecl.parseBAPIAsIRTypedeclCStringDecl));

        lexer.ensureAndConsumeSymbol("List<Assembly::StringTypeDecl>");
        irasm.stringoftypedecls.push(...parseListOf<IRTypedeclStringDecl>(lexer, '{', '}', ',', IRTypedeclStringDecl.parseBAPIAsIRTypedeclStringDecl));

        lexer.ensureAndConsumeSymbol("Map<Assembly::TypeKey, Assembly::AbstractNominalTypeDecl>");
        const entrylist = parseListOf<[string, IRAbstractNominalTypeDecl]>(lexer, '{', '}', ',', (lexer) => {
            const key = parseTypeKey(lexer);
            lexer.ensureAndConsumeSymbol('=>');
            const value = IRAbstractNominalTypeDecl.parseBAPI(lexer);
            return [key, value];
        });
        entrylist.forEach(([k, v]) => irasm.alltypes.set(k, v));

        lexer.ensureAndConsumeSymbol("List<Assembly::EListTypeSignature>");
        irasm.elists.push(...parseListOf<IREListTypeSignature>(lexer, '{', '}', ',', IREListTypeSignature.parseBAPIAsIREListTypeSignature));

        lexer.ensureAndConsumeSymbol("}");

        return irasm;
    }
}

export {
    IRPreConditionDecl, IRPostConditionDecl, IRInvariantDecl, IRValidateDecl,
    IRDeclarationDocString, IRDeclarationMetaTag,
    IRConstantDecl,
    IRInvokeParameterDecl, IRInvokeMetaDecl, IRTestAssociation,
    IRTestDecl, IRExampleDecl, IRInvokeDecl, IRTaskActionDecl,
    IRMemberFieldDecl,
    IRAbstractNominalTypeDecl, IRAbstractEntityTypeDecl, 
    IREnumTypeDecl, 
    IRTypedeclTypeDecl, IRTypedeclCStringDecl, IRTypedeclStringDecl,
    IRInternalEntityTypeDecl, IRPrimitiveEntityTypeDecl, IRConstructableTypeDecl, 
    IROkTypeDecl, IRFailTypeDecl,
    IRAPIDeniedTypeDecl, IRAPIErrorTypeDecl, IRAPIRejectedTypeDecl, IRAPIFlaggedTypeDecl, IRAPISuccessTypeDecl,
    IRSomeTypeDecl, IRMapEntryTypeDecl,
    IRAbstractCollectionTypeDecl, IRListTypeDecl, IRStackTypeDecl, IRQueueTypeDecl, IRSetTypeDecl, IRMapTypeDecl,
    IREventListTypeDecl,
    IREntityTypeDecl,
    IRAbstractConceptTypeDecl, IRInternalConceptTypeDecl,
    IROptionTypeDecl, IRResultTypeDecl, IRAPIResultTypeDecl, 
    IRConceptTypeDecl,
    IRDatatypeMemberEntityTypeDecl, IRDatatypeTypeDecl,
    IREnvironmentVariableInformation, IRResourceInformation, IRTaskConfiguration,
    IRAPIDecl, IRAgentDecl, IRTaskDecl,
    IRLambdaParameterPackDecl,
    IRAssembly
};
