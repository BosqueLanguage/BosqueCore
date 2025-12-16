import { SourceInfo } from "../../frontend/build_decls";
import { IRNominalTypeSignature, IRTypeSignature } from "./irtype";
import { IRSimpleExpression, IRStatement } from "./irbody";
import { IRRegex } from "./irsupport";

abstract class IRConditionDecl {
    readonly file: string;
    readonly sinfo: SourceInfo;

    readonly diagnosticTag: string | undefined;
    
    readonly stmts: IRStatement[];
    readonly value: IRSimpleExpression;

    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined, stmts: IRStatement[], value: IRSimpleExpression) {
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

    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, ikey: string, requiresidx: number, issoft: boolean, stmts: IRStatement[], value: IRSimpleExpression) {
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
    
    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, ikey: string, ensuresidx: number, issoft: boolean, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.ikey = ikey;
        this.ensuresidx = ensuresidx;
        this.issoft = issoft;
    }
}

class IRInvariantDecl extends IRConditionDecl {
    readonly tkey: string;
    readonly invariantidx: number;
    
    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, tkey: string, invariantidx: number, stmts: IRStatement[], value: IRSimpleExpression) {
        super(file, sinfo, tag, stmts, value);
        this.tkey = tkey;
        this.invariantidx = invariantidx;
    }
}

class IRValidateDecl extends IRConditionDecl {
    readonly tkey: string;
    readonly validateidx: number;
    
    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, tkey: string, validateidx: number, stmts: IRStatement[], value: IRSimpleExpression) {
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



/////////////////////////////////////////////////

class IRConstMemberDecl {
    readonly ckey: string;

    readonly enclosingType: IRNominalTypeSignature;
    readonly declaredType: IRTypeSignature;
    readonly stmts: IRStatement[];
    readonly value: IRSimpleExpression;

    readonly docstr: IRDeclarationDocString | undefined;

    constructor(ckey: string, enclosingType: IRNominalTypeSignature, declaredType: IRTypeSignature, stmts: IRStatement[], value: IRSimpleExpression, docstr: IRDeclarationDocString | undefined) {
        this.ckey = ckey;
        this.enclosingType = enclosingType;
        this.declaredType = declaredType;
        this.stmts = stmts;
        this.value = value;
        this.docstr = docstr;
    }
}

class IRMemberFieldDecl {
    readonly fkey: string;

    readonly enclosingType: IRNominalTypeSignature;
    readonly name: string;
    readonly declaredType: IRTypeSignature;
    readonly defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined;

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    constructor(fkey: string, enclosingType: IRNominalTypeSignature, name: string, declaredType: IRTypeSignature, defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined, docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[]) {
        this.fkey = fkey;
        this.enclosingType = enclosingType;
        this.name = name;
        this.declaredType = declaredType;
        this.defaultValue = defaultValue;

        this.docstr = docstr;
        this.metatags = metatags;
    }
}

enum IRAdditionalTypeDeclTag {
    Std,
    Status,
    Event
}

abstract class IRAbstractNominalTypeDecl {
    readonly tkey: string;

    readonly invariants: IRInvariantDecl[];
    readonly validates: IRValidateDecl[];

    readonly consts: IRConstMemberDecl[];
    readonly fields: IRMemberFieldDecl[];
    readonly functions: IRInvokeDecl[];
    readonly methods: IRMethodDecl[];

    readonly etag: IRAdditionalTypeDeclTag;

    readonly saturatedProvides: IRTypeSignature[];
    readonly saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[];

    readonly allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[];
    readonly allValidates: { containingtype: IRNominalTypeSignature, ii: number }[];
    
    //TODO vtable info here

    readonly docstr: IRDeclarationDocString | undefined;
    readonly metatags: IRDeclarationMetaTag[];

    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], consts: IRConstMemberDecl[], fields: IRMemberFieldDecl[], functions: IRInvokeDecl[], methods: IRMethodDecl[], etag: IRAdditionalTypeDeclTag, saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[]) {
        this.tkey = tkey;

        this.invariants = invariants;
        this.validates = validates;

        this.consts = consts;
        this.fields = fields;
        this.functions = functions;
        this.methods = methods;

        this.etag = etag;

        this.saturatedProvides = saturatedProvides;
        this.saturatedBFieldInfo = saturatedBFieldInfo;

        this.allInvariants = allInvariants;
        this.allValidates = allValidates;

        this.docstr = docstr;
        this.metatags = metatags;
    }
}

abstract class IRAbstractEntityTypeDecl extends IRAbstractNominalTypeDecl {
    constructor(tkey: string, invariants: IRInvariantDecl[], validates: IRValidateDecl[], consts: IRConstMemberDecl[], fields: IRMemberFieldDecl[], functions: IRInvokeDecl[], methods: IRMethodDecl[], etag: IRAdditionalTypeDeclTag, saturatedProvides: IRTypeSignature[], saturatedBFieldInfo: { containingtype: IRNominalTypeSignature, fkey: string }[], allInvariants: { containingtype: IRNominalTypeSignature, ii: number }[], allValidates: { containingtype: IRNominalTypeSignature, ii: number }[], docstr: IRDeclarationDocString | undefined, metatags: IRDeclarationMetaTag[]) {
        super(tkey, invariants, validates, consts, fields, functions, methods, etag, saturatedProvides, saturatedBFieldInfo, allInvariants, allValidates, docstr, metatags);
    }
}

class IREnumTypeDecl extends IRAbstractEntityTypeDecl {
    readonly members: string[];

    xxxx;
}

class IRTypedeclTypeDecl extends IRAbstractEntityTypeDecl {
    valuetype: IRTypeSignature;
    
    xxxx;
}

xxxx; //string versions
class IRTypedeclTypeDecl extends IRAbstractEntityTypeDecl {
    valuetype: IRTypeSignature;
    
    xxxx;
}

/////////////////////////////////////////////////

class IRAssembly {
    readonly regexps: IRRegex[];

    constructor(regexps: IRRegex[]) {
        this.regexps = regexps;
    }
}

export {
    IRPreConditionDecl, IRPostConditionDecl, IRInvariantDecl, IRValidateDecl,
    IRDeclarationDocString, IRDeclarationMetaTag,
    IRAssembly
};