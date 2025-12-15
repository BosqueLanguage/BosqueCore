import { SourceInfo } from "../../frontend/build_decls";
import { IRTypeSignature } from "./irtype";
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

    constructor(name: string, tags: {enumType: IRTypeSignature, tag: string}[], text: string | undefined) {
        this.name = name;
        this.tags = tags;
    }
}

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