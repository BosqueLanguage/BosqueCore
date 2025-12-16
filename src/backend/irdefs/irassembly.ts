<<<<<<< HEAD
import { IRTypeSignature } from "./irtype";
=======
import { SourceInfo } from "../../frontend/build_decls";
import { IRNominalTypeSignature, IRTypeSignature } from "./irtype";
>>>>>>> refs/remotes/origin/11_18_go2_checker
import { IRSimpleExpression, IRStatement } from "./irbody";
import { IRRegex, IRSourceInfo } from "./irsupport";

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


/////////////////////////////////////////////////

class IRInvokeParameterDecl {
    readonly name: string;
    readonly type: IRTypeSignature;
    readonly pkind: "ref" | "out" | "out?" | "inout" | undefined;
    
    constructor(name: string, type: TypeSignature, optDefaultValue: Expression | undefined, pkind: "ref" | "out" | "out?" | "inout" | undefined, isRestParam: boolean) {
        this.name = name;
        this.type = type;
        this.optDefaultValue = optDefaultValue;
        this.pkind = pkind;
        this.isRestParam = isRestParam;
    }

    emit(fmt: CodeFormatter): string {
        const tdecl = this.type instanceof AutoTypeSignature ? "" : `: ${this.type.emit()}`;
        const defv = this.optDefaultValue === undefined ? "" : ` = ${this.optDefaultValue.emit(true, fmt)}`;
        return `${(this.pkind ? this.pkind + " " : "")}${this.isRestParam ? "..." : ""}${this.name}${tdecl}${defv}`;
    }
}

abstract class AbstractInvokeDecl extends AbstractCoreDecl {
    readonly recursive: RecursiveAnnotation;

    readonly params: InvokeParameterDecl[];
    readonly resultType: TypeSignature;

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation) {
        super(file, sinfo, attributes, name);

        this.recursive = recursive;

        this.params = params;
        this.resultType = resultType;

        this.body = body;
    }

    emitSig(fmt: CodeFormatter): [string, string] {
        const attrs = this.emitAttributes();

        let rec = "";
        if (this.recursive !== "no") {
            rec = this.recursive === "yes" ? "recursive " : "recursive? ";
        }

        let params = this.params.map((p) => p.emit(fmt)).join(", ");
        let result = (this.resultType instanceof VoidTypeSignature) ? "" : (": " + this.resultType.emit());

        return [`${attrs}${rec}`, `(${params})${result}`];
    }
}


abstract class ExplicitInvokeDecl extends AbstractInvokeDecl {
    readonly terms: InvokeTemplateTermDecl[];
    readonly termRestriction: InvokeTemplateTypeRestriction | undefined;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[]) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body);

        this.terms = terms;
        this.termRestriction = termRestriction;

        this.preconditions = preconditions;
        this.postconditions = postconditions;
    }

    emitMetaInfo(fmt: CodeFormatter): string | undefined {
        let prec: string[] = [];
        if(this.preconditions.length !== 0) {
            prec = this.preconditions.map((pc) => pc.emit(fmt));
        }

        let postc: string[] = [];
        if(this.postconditions.length !== 0) {
            postc = this.postconditions.map((pc) => pc.emit(fmt));
        }

        if(prec.length === 0 && postc.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc].join("\n");
        }
    }

    emit(fmt: CodeFormatter): string {
        const ssig = this.emitSig(fmt);
        const meta = this.emitMetaInfo(fmt);

        let terms = "";
        if(this.terms.length !== 0) {
            terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
        }

        let restricts = "";
        if (this.termRestriction !== undefined) {
            restricts = this.termRestriction.emit() + " ";
        }

        const ttinfo = this.getDeclarationTag();

        return (fmt as CodeFormatter).indent(`${ssig[0]} ${ttinfo} ${restricts}${this.name}${terms}${ssig[1]} ${this.body.emit(fmt, meta)}`);
    }

    abstract getDeclarationTag(): string;
}

abstract class FunctionInvokeDecl extends ExplicitInvokeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[]) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions);
    }
}

class TestAssociation {
    readonly file: string;
    readonly ns: FullyQualifiedNamespace;
    readonly ontype: string | undefined;
    readonly onmember: string | undefined;

    constructor(file: string, ns: FullyQualifiedNamespace, ontype: string | undefined, onmember: string | undefined) {
        this.file = file;
        this.ns = ns;
        this.ontype = ontype;
        this.onmember = onmember;
    }

    isMatchWith(tmatch: TestAssociation): boolean {
        if(!FullyQualifiedNamespace.areSame(this.ns, tmatch.ns)) {
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

class NamespaceFunctionDecl extends FunctionInvokeDecl {
    readonly fkind: "function" | "predicate" | "errtest" | "chktest" | "example";
    readonly tassoc: TestAssociation[] | undefined;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], tassoc: TestAssociation[] | undefined, fkind: "function" | "predicate" | "errtest" | "chktest" | "example") {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions);

        this.fkind = fkind;
        this.tassoc = tassoc;
    }

    getDeclarationTag(): string {
        return this.fkind;
    }
}

class TypeFunctionDecl extends FunctionInvokeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[]) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions);
    }

    getDeclarationTag(): string {
        return "function";
    }
}

class MethodDecl extends ExplicitInvokeDecl {
    readonly isThisRef: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], isThisRef: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions);

        this.isThisRef = isThisRef;
    }

    getDeclarationTag(): string {
        return (this.isThisRef ? "ref " : "") + "method";
    }
}

class TaskMethodDecl extends ExplicitInvokeDecl {
    readonly isSelfRef: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], isSelfRef: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions);

        this.isSelfRef = isSelfRef;
    }

    getDeclarationTag(): string {
        return (this.isSelfRef ? "ref " : "") + "method";
    }
}

class TaskActionDecl extends ExplicitInvokeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[]) {
        super(file, sinfo, attributes, name, "no", params, resultType, body, terms, termRestriction, preconditions, postconditions);
    }

    getDeclarationTag(): string {
        return "action";
    }
}


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