
import { FullyQualifiedNamespace, TypeSignature, LambdaTypeSignature, RecursiveAnnotation, TemplateTypeSignature, VoidTypeSignature, LambdaParameterSignature, AutoTypeSignature, NominalTypeSignature } from "./type.js";
import { Expression, BodyImplementation, ExpressionTag, AccessNamespaceConstantExpression, LiteralRegexExpression, ChkLogicExpression } from "./body.js";

import { BuildLevel, CodeFormatter, SourceInfo } from "./build_decls.js";

const s_p62bit_safe = 4611686018427387903n;
const s_p124bit_safe = s_p62bit_safe * s_p62bit_safe; 

const MIN_SAFE_INT = -s_p62bit_safe;
const MAX_SAFE_INT = s_p62bit_safe;

const MIN_SAFE_CHK_INT = -s_p124bit_safe;
const MAX_SAFE_CHK_INT = s_p124bit_safe;

//negation and conversion are always safe
const MAX_SAFE_NAT = s_p62bit_safe;
const MAX_SAFE_CHK_NAT = s_p124bit_safe;

const WELL_KNOWN_RETURN_VAR_NAME = "$return";
const WELL_KNOWN_EVENTS_VAR_NAME = "$events";

enum TemplateTermDeclExtraTag {
    KeyType = "keytype",
    Numeric = "numeric",
    Equiv = "equiv",
    Mergeable = "mergeable"
}

class TemplateTermDecl {
    readonly name: string;
    readonly tconstraint: TypeSignature | undefined;
    readonly extraTags: TemplateTermDeclExtraTag[];

    constructor(name: string, tconstraint: TypeSignature | undefined, extraTags: TemplateTermDeclExtraTag[]) {
        this.name = name;
        this.tconstraint = tconstraint;
        this.extraTags = extraTags;
    }

    emitHelper(): string {
        let chks: string[] = this.extraTags.map((t) => t);  

        if(this.tconstraint !== undefined) {
            chks.push(this.tconstraint.emit());
        }

        const tstr = (chks.length !== 0) ? `: ${chks.join(" ")}` : "";
        return `${this.name}${tstr}`;
    }
}

class TypeTemplateTermDecl extends TemplateTermDecl {
    constructor(name: string, tags: TemplateTermDeclExtraTag[], tconstraint: TypeSignature | undefined) {
        super(name, tconstraint, tags);
    }

    emit(): string {
        return this.emitHelper();
    }
}

class InvokeTemplateTermDecl extends TemplateTermDecl {
    readonly caninfer: boolean;

    constructor(name: string, tags: TemplateTermDeclExtraTag[], tconstraint: TypeSignature | undefined, caninfer: boolean) {
        super(name, tconstraint, tags);
        this.caninfer = caninfer;
    }

    emit(): string {
        return this.emitHelper() + (this.caninfer ? "?" : "");
    }
}

class InvokeTemplateTypeRestrictionClause {
    readonly t: TemplateTypeSignature;
    readonly subtype: TypeSignature | undefined;
    readonly extraTags: TemplateTermDeclExtraTag[];

    constructor(t: TemplateTypeSignature, subtype: TypeSignature | undefined, extraTags: TemplateTermDeclExtraTag[]) {
        this.t = t;
        this.subtype = subtype;
        this.extraTags = extraTags;
    }

    emit(): string {
        let chks: string[] = this.extraTags.map((t) => t);

        if(this.subtype !== undefined) {
            chks.push(this.subtype.emit());
        }

        const tstr = chks.length !== 0 ? `: ${chks.join(" ")}` : "";
        return `${this.t}${tstr}`;
    }
}

class InvokeTemplateTypeRestriction {
    readonly clauses: InvokeTemplateTypeRestrictionClause[];

    constructor(clauses: InvokeTemplateTypeRestrictionClause[]) {
        this.clauses = clauses;
    }

    emit(): string {
        return `{when ${this.clauses.map((c) => c.emit()).join(", ")}}`;
    }
}

class TaskConfiguration {
    timeout: number | undefined;
    retry: {delay: number, tries: number} | undefined;
    priority: "immediate" | "fast" | "normal" | "longrunning" | "background" | "optional" | undefined;

    constructor(timeout: number | undefined, retry: {delay: number, tries: number} | undefined, priority: "immediate" | "fast" | "normal" | "longrunning" | "background" | "optional" | undefined) {
        this.timeout = timeout;
        this.retry = retry;
        this.priority = priority;
    }

    emit(): string | undefined {
        if(this.priority === undefined && this.retry !== undefined && this.timeout !== undefined) {
            return undefined;
        }

        const cs = [
            this.timeout !== undefined ? `timeout=${this.timeout}ms` : undefined,
            this.retry !== undefined ? `retry=(${this.retry.tries}@${this.retry.delay}ms)` : undefined,
            this.priority !== undefined ? `priority=${this.priority}` : undefined
        ].filter((c) => c !== undefined) as string[];

        return cs.join(", ");
    }
}

abstract class AbstractDecl {
    readonly file: string;
    readonly sinfo: SourceInfo;

    constructor(file: string, sinfo: SourceInfo) {
        this.file = file;
        this.sinfo = sinfo;
    }

    abstract emit(fmt: CodeFormatter): string;
}

abstract class ConditionDecl extends AbstractDecl {
    readonly diagnosticTag: string | undefined;

    constructor(file: string, sinfo: SourceInfo, diagnosticTag: string | undefined) {
        super(file, sinfo);
        this.diagnosticTag = diagnosticTag;
    }

    emitDiagnosticTag(): string {
        return this.diagnosticTag === undefined ? "" : `[${this.diagnosticTag}]`;
    }
}

class PreConditionDecl extends ConditionDecl {
    readonly level: BuildLevel;
    readonly issoft: boolean;
    readonly exp: ChkLogicExpression;

    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, level: BuildLevel, issoft: boolean, exp: ChkLogicExpression) {
        super(file, sinfo, tag);

        this.level = level;
        this.issoft = issoft;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("requires" + this.emitDiagnosticTag() + (this.issoft ? " softcheck" : "") + (this.level !== "release" ? (" " + this.level) : "") + " " + this.exp.emit(fmt) + ";");
    }
}

class PostConditionDecl extends ConditionDecl {
    readonly level: BuildLevel;
    readonly issoft: boolean;
    readonly exp: ChkLogicExpression;

    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, level: BuildLevel, issoft: boolean, exp: ChkLogicExpression) {
        super(file, sinfo, tag);

        this.level = level;
        this.issoft = issoft;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("ensures" + this.emitDiagnosticTag() + (this.issoft ? " softcheck" : "") + (this.level !== "release" ? (" " + this.level) : "") + " " + this.exp.emit(fmt) + ";");
    }
}

class InvariantDecl extends ConditionDecl {
    readonly ii: number;
    readonly level: BuildLevel;
    readonly exp: ChkLogicExpression;

    constructor(file: string, sinfo: SourceInfo, ii: number, tag: string | undefined, level: BuildLevel, exp: ChkLogicExpression) {
        super(file, sinfo, tag);

        this.ii = ii;
        this.level = level;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("invariant" + this.emitDiagnosticTag() + (this.level !== "release" ? (" " + this.level) : "") + " " + this.exp.emit(fmt) + ";");
    }
}

class ValidateDecl extends ConditionDecl {
    readonly ii: number;
    readonly exp: ChkLogicExpression;

    constructor(file: string, sinfo: SourceInfo, ii: number, tag: string | undefined, exp: ChkLogicExpression) {
        super(file, sinfo, tag);

        this.ii = ii;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("validate" + this.emitDiagnosticTag() + " " + this.exp.emit(fmt) + ";");
    }
}

class DeclarationAttibute {
    readonly name: string;
    readonly tags: {enumType: TypeSignature, tag: string}[]; //tags are enum names
    readonly text: string | undefined;

    constructor(name: string, tags: {enumType: TypeSignature, tag: string}[], text: string | undefined) {
        this.name = name;
        this.tags = tags;
        this.text = text;
    }

    emit(): string {
        if(this.name === "doc") {
            return `%** ${this.text} **%`;
        }
        else {
            return `${this.name}${this.tags.length === 0 ? "" : " [" + this.tags.map((t) => `${t.enumType.emit()}::${t.tag}`).join(", ") + "]"}`;
        }
    }
}

abstract class AbstractCoreDecl extends AbstractDecl {
    readonly attributes: DeclarationAttibute[];
    readonly name: string;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo);
        
        this.attributes = attributes;
        this.name = name;
    }

    hasAttribute(aname: string): boolean {
        return this.attributes.find((attr) => attr.name === aname) !== undefined;
    }

    emitAttributes(): string {
        return this.attributes.length !== 0 ? (this.attributes.map((attr) => attr.emit()).join(" ") + " ") : "";
    }
}

class InvokeParameterDecl {
    readonly name: string;
    readonly type: TypeSignature;
    readonly optDefaultValue: Expression | undefined;
    readonly pkind: "ref" | "out" | "out?" | "inout" | undefined;
    readonly isRestParam: boolean;

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

class LambdaDecl extends AbstractInvokeDecl {
    readonly isAuto: boolean;

    capturedVars: {name: string, type: TypeSignature}[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: "fn" | "pred", recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, isAuto: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body);

        this.isAuto = isAuto;
    }

    generateSig(sinfo: SourceInfo): TypeSignature {
        const lpsigs = this.params.map((p) => new LambdaParameterSignature(p.name, p.type, p.pkind, p.isRestParam));
        return new LambdaTypeSignature(sinfo, this.recursive, this.name as ("fn" | "pred"), lpsigs, this.resultType);
    }

    override emitSig(fmt: CodeFormatter): [string, string] {
        const attrs = this.emitAttributes();

        let rec = "";
        if (this.recursive !== "no") {
            rec = this.recursive === "yes" ? "recursive " : "recursive? ";
        }

        let params = this.params.map((p) => p.emit(fmt)).join(", ");
        let result = (this.resultType instanceof AutoTypeSignature) ? "" : (": " + this.resultType.emit());

        return [`${attrs}${rec}`, `(${params})${result}`];
    }

    emit(fmt: CodeFormatter): string {
        const ssig = this.emitSig(fmt);

        return `${ssig[0]}${this.name}${ssig[1]} => ${this.body.emit(fmt, undefined)}`;
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

class ConstMemberDecl extends AbstractCoreDecl {
    readonly declaredType: TypeSignature;
    readonly value: Expression;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, value: Expression) {
        super(file, sinfo, attributes, name);

        this.declaredType = dtype;
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}const ${this.name}: ${this.declaredType.emit()} = ${this.value.emit(true, fmt)};`);
    }
}

class MemberFieldDecl extends AbstractCoreDecl {
    readonly declaredType: TypeSignature;
    readonly defaultValue: Expression | undefined;
    readonly isSpecialAccess: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, dvalue: Expression | undefined, isSpecialAccess: boolean) {
        super(file, sinfo, attributes, name);
        
        this.declaredType = dtype;
        this.defaultValue = dvalue;
        this.isSpecialAccess = isSpecialAccess;
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        if(this.defaultValue === undefined) {
            return fmt.indent(`${attrs}field ${this.name}: ${this.declaredType.emit()};`);
        }
        else {
            return fmt.indent(`${attrs}field ${this.name}: ${this.declaredType.emit()} = ${this.defaultValue.emit(true, fmt)};`);
        }
    }
}

enum AdditionalTypeDeclTag {
    Std,
    Status,
    Event
}

abstract class AbstractNominalTypeDecl extends AbstractDecl {
    readonly attributes: DeclarationAttibute[];
    readonly ns: FullyQualifiedNamespace;
    readonly name: string;

    readonly terms: TypeTemplateTermDecl[] = [];
    readonly provides: TypeSignature[] = [];

    readonly invariants: InvariantDecl[] = [];
    readonly validates: ValidateDecl[] = [];

    readonly consts: ConstMemberDecl[] = [];
    readonly functions: TypeFunctionDecl[] = [];
    readonly methods: MethodDecl[] = [];

    readonly etag: AdditionalTypeDeclTag;

    saturatedProvides: TypeSignature[] = [];
    saturatedBFieldInfo: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[] = [];

    allInvariants: {containingtype: NominalTypeSignature, ii: number, file: string, sinfo: SourceInfo, tag: string | undefined}[] = [];
    allValidates: {containingtype: NominalTypeSignature, ii: number, file: string, sinfo: SourceInfo, tag: string | undefined}[] = [];

    hasDynamicInvokes: boolean = false;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag) {
        super(file, sinfo);

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.etag = etag;
    }

    //These are our annoying nested types
    isSpecialResultEntity(): boolean { return (this instanceof OkTypeDecl) || (this instanceof FailTypeDecl); }
    isSpecialAPIResultEntity(): boolean { return (this instanceof APIErrorTypeDecl) || (this instanceof APIRejectedTypeDecl) || (this instanceof APIDeniedTypeDecl) || (this instanceof APIFlaggedTypeDecl) || (this instanceof APISuccessTypeDecl); }

    hasAttribute(aname: string): boolean {
        return this.attributes.find((attr) => attr.name === aname) !== undefined;
    }

    emitAttributes(): string {
        return this.attributes.length !== 0 ? (this.attributes.map((attr) => attr.emit()).join(" ") + " ") : "";
    }

    emitAdditionalTag(): string {
        switch(this.etag) {
            case AdditionalTypeDeclTag.Status: return "status ";
            case AdditionalTypeDeclTag.Event: return "event ";
            default: return "";
        }
    }

    isKeyTypeRestricted(): boolean {
        return this.attributes.find((attr) => attr.name === "__keycomparable") !== undefined;
    }

    isNumericRestricted(): boolean {
        return this.attributes.find((attr) => attr.name === "__numeric") !== undefined;
    }

    isEquivRestricted(): boolean {
        return this.attributes.find((attr) => attr.name === "equiv") !== undefined;
    }

    isMergeableRestricted(): boolean {
        return this.attributes.find((attr) => attr.name === "mergeable") !== undefined;
    }

    emitTerms(): string {
        return this.terms.length !== 0 ? ("<" + this.terms.map((tt) => tt.emit()).join(", ") + ">") : "";
    }

    emitProvides(): string {
        return this.provides.length !== 0 ? (" provides" + this.provides.map((p) => p.emit()).join(", ")) : "";
    }

    emitBodyGroups(fmt: CodeFormatter): string[][] {
        const groups: string[][] = [];

        if(this.consts.length !== 0) {
            groups.push(this.consts.map((c) => c.emit(fmt)));
        }

        if(this.functions.length !== 0) {
            groups.push(this.functions.map((f) => f.emit(fmt)));
        }

        if(this.methods.length !== 0) {
            groups.push(this.methods.map((m) => m.emit(fmt)));
        }

        return groups;
    }

    joinBodyGroups(groups: string[][]): string {
        return groups.map((g) => g.join("\n")).join("\n\n");
    }
}

abstract class AbstractEntityTypeDecl extends AbstractNominalTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag) {
        super(file, sinfo, attributes, ns, name, etag);
    }
}

class EnumTypeDecl extends AbstractEntityTypeDecl {
    readonly members: string[];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, members: string[], etag: AdditionalTypeDeclTag) {
        super(file, sinfo, attributes, ns, name, etag);

        this.members = members;
    }

    emit(fmt: CodeFormatter): string {
        fmt.indentPush();
        const endl = this.members.map((e) => fmt.indent(e + ",")).join("\n");
        fmt.indentPop();

        return fmt.indent(`${this.emitAttributes()}${this.emitAdditionalTag()}enum ${this.name} {${endl}${fmt.indent("\n}")}`);
    }
}

class TypedeclTypeDecl extends AbstractEntityTypeDecl {
    valuetype: TypeSignature;
    optofexp: Expression | undefined; //for strings, cstrings, and paths (but not fragments or globs)

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag, valuetype: TypeSignature) {
        super(file, sinfo, attributes, ns, name, etag);

        this.valuetype = valuetype;
    }

    emit(fmt: CodeFormatter): string {
        const tdcl = `${this.emitAttributes()}${this.emitAdditionalTag()}type ${this.name}${this.emitTerms()} = ${this.valuetype.emit()}`;

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        let ofexp = "";
        if(this.optofexp !== undefined) {
            ofexp = ` of ${this.optofexp.emit(true, fmt)}`;
        }

        if(bg.length === 0 && this.provides.length === 0) {
            return tdcl + ofexp + ";";
        }
        else {
            return tdcl + ofexp + " &" + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
        }
    }
}

abstract class InternalEntityTypeDecl extends AbstractEntityTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, new FullyQualifiedNamespace(["Core"]) , name, AdditionalTypeDeclTag.Std);
    }
}

class PrimitiveEntityTypeDecl extends InternalEntityTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

abstract class ConstructableTypeDecl extends InternalEntityTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class OkTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class FailTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class APIErrorTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class APIRejectedTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class APIDeniedTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class APIFlaggedTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class APISuccessTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class SomeTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class MapEntryTypeDecl extends ConstructableTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

abstract class AbstractCollectionTypeDecl extends InternalEntityTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class ListTypeDecl extends AbstractCollectionTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class StackTypeDecl extends AbstractCollectionTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class QueueTypeDecl extends AbstractCollectionTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class SetTypeDecl extends AbstractCollectionTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class MapTypeDecl extends AbstractCollectionTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class EventListTypeDecl extends AbstractCollectionTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class EntityTypeDecl extends AbstractEntityTypeDecl {
    readonly fields: MemberFieldDecl[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag) {
        super(file, sinfo, attributes, ns, name, etag);
    }

    emit(fmt: CodeFormatter): string {
        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.fields.length !== 0) {
            bg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        return `${this.emitAttributes()}${this.emitAdditionalTag()}entity ${this.name}${this.emitTerms()} ${this.emitProvides()} {\n ${this.joinBodyGroups(bg)}${fmt.indent("\n}")}`;
    }
}

abstract class AbstractConceptTypeDecl extends AbstractNominalTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag) {
        super(file, sinfo, attributes, ns, name, etag);
    }
}

abstract class InternalConceptTypeDecl extends AbstractConceptTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, new FullyQualifiedNamespace(["Core"]), name, AdditionalTypeDeclTag.Std);
    }
}

class OptionTypeDecl extends InternalConceptTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
    
    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "concept " + this.name + this.emitTerms() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class ResultTypeDecl extends InternalConceptTypeDecl {
    readonly nestedEntityDecls: (OkTypeDecl | FailTypeDecl)[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    getOkType(): OkTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof OkTypeDecl) as OkTypeDecl;
    }

    getFailType(): FailTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof FailTypeDecl) as FailTypeDecl;
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.nestedEntityDecls.length !== 0) {
            bg.push(this.nestedEntityDecls.map((ned) => ned.emit(fmt)));
        }
        fmt.indentPop();

        return attrs + "concept " + this.name + this.emitTerms() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class APIResultTypeDecl extends InternalConceptTypeDecl {
    readonly nestedEntityDecls: (APIErrorTypeDecl | APIRejectedTypeDecl | APIDeniedTypeDecl | APIFlaggedTypeDecl | APISuccessTypeDecl)[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    getAPIErrorType(): APIErrorTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof APIErrorTypeDecl) as APIErrorTypeDecl;
    }

    getAPIRejectedType(): APIRejectedTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof APIRejectedTypeDecl) as APIRejectedTypeDecl;
    }

    getAPIDeniedType(): APIDeniedTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof APIDeniedTypeDecl) as APIDeniedTypeDecl;
    }
    
    getAPIFlaggedType(): APIFlaggedTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof APIFlaggedTypeDecl) as APIFlaggedTypeDecl;
    }

    getAPISuccessType(): APISuccessTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof APISuccessTypeDecl) as APISuccessTypeDecl;
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.nestedEntityDecls.length !== 0) {
            bg.push(this.nestedEntityDecls.map((ned) => ned.emit(fmt)));
        }
        fmt.indentPop();

        return attrs + "concept " + this.name + this.emitTerms() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class ConceptTypeDecl extends AbstractConceptTypeDecl {
    readonly fields: MemberFieldDecl[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag) {
        super(file, sinfo, attributes, ns, name, etag);
    }

    emit(fmt: CodeFormatter): string {
        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.fields.length !== 0) {
            bg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        return `${this.emitAttributes}${this.emitAdditionalTag()}concept ${this.name}${this.emitTerms()} ${this.emitProvides()} {\n${this.joinBodyGroups(bg)}${fmt.indent("\n")}}`;
    }
}

class DatatypeMemberEntityTypeDecl extends AbstractEntityTypeDecl {
    readonly fields: MemberFieldDecl[] = [];
    readonly parentTypeDecl: DatatypeTypeDecl;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag, parentTypeDecl: DatatypeTypeDecl) {
        super(file, sinfo, attributes, ns, name, etag);

        this.parentTypeDecl = parentTypeDecl;
    }

    emit(fmt: CodeFormatter): string {
        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.fields.length !== 0) {
            bg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        return this.name + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class DatatypeTypeDecl extends AbstractConceptTypeDecl {
    readonly fields: MemberFieldDecl[] = [];
    readonly associatedMemberEntityDecls: DatatypeMemberEntityTypeDecl[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag) {
        super(file, sinfo, attributes, ns, name, etag);
    }

    emit(fmt: CodeFormatter): string {
        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);

        const mg: string[][] = [];
        if(this.fields.length !== 0) {
            mg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        const rootdecl = `${this.emitAttributes()}${this.emitAdditionalTag()}datatype ${this.name}${this.emitTerms()} ${this.emitProvides()}`; 
        let usingdecl = " of\n";
        if(mg.length !== 0 && bg.length === 0) {
            usingdecl = " using {\n" + this.joinBodyGroups(mg) + fmt.indent("\n}\nof\n");
        }

        const edecls = this.associatedMemberEntityDecls.map((aed) => aed.emit(fmt)).join("\n| ");

        let etail = ";";
        if(bg.length !== 0) {
            etail = "& {\n" + this.joinBodyGroups([...mg, ...bg]) + fmt.indent("\n}");
        }

        return `${rootdecl}${usingdecl}${edecls}\n${etail}`;
    }
}

class EnvironmentVariableInformation {
    readonly evname: string; //identifier or cstring
    readonly evtype: TypeSignature;
    readonly required: boolean;
    readonly optdefault: Expression | undefined;

    constructor(evname: string, evtype: TypeSignature, required: boolean, optdefault: Expression | undefined) {
        this.evname = evname;
        this.evtype = evtype;
        this.required = required;
        this.optdefault = optdefault;
    }

    emit(fmt: CodeFormatter): string {
        const optional = this.required ? "" : "?";
        if(this.optdefault === undefined) {
            return fmt.indent(`${this.evname}${optional}: ${this.evtype.emit()}`);
        }
        else {
            return fmt.indent(`${this.evname}${optional}: ${this.evtype.emit()} = ${this.optdefault.emit(true, fmt)}`);
        }
    }
}

class ResourceInformation {
    readonly pathglobs: { pg: Expression[], optas: Expression | undefined }[]; //Literal glob, constant refernence, or env var reference

    constructor(pathglobs: { pg: Expression[], optas: Expression | undefined }[]) {
        this.pathglobs = pathglobs;
    }

    static emitSingleRInfo(fmt: CodeFormatter, pg: Expression[], optas: Expression | undefined): string {
        if(optas === undefined) {
            if(pg.length === 1) {
                return fmt.indent(pg[0].emit(true, fmt));
            }
            else {
                return fmt.indent(`[${pg.map((pge) => pge.emit(true, fmt)).join(", ")}]`);
            }
        }
        else {
            if(pg.length === 1) {
                return fmt.indent(`${pg[0].emit(true, fmt)} as ${optas.emit(true, fmt)}`);
            }
            else {
                return fmt.indent(`[${pg.map((pge) => pge.emit(true, fmt)).join(", ")}] as ${optas.emit(true, fmt)}`);
            }
        }
    }
}

class APIDecl extends AbstractCoreDecl {
    readonly params: InvokeParameterDecl[];    
    readonly resultType: TypeSignature;
    readonly eventType: TypeSignature | undefined;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly configs: TaskConfiguration;

    readonly statusinfo: TypeSignature[];
    readonly envreqs: EnvironmentVariableInformation[];
    readonly resourcereqs: ResourceInformation;

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: InvokeParameterDecl[], resultType: TypeSignature, eventType: TypeSignature | undefined, preconds: PreConditionDecl[], postconds: PostConditionDecl[], configs: TaskConfiguration, statusinfo: TypeSignature[], envreqs: EnvironmentVariableInformation[], resourcereqs: ResourceInformation, body: BodyImplementation) {
        super(file, sinfo, attributes, name);

        this.params = params;
        this.resultType = resultType;
        this.eventType = eventType;

        this.preconditions = preconds;
        this.postconditions = postconds

        this.configs = configs;

        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;

        this.body = body;
    }

    emitMetaInfo(fmt: CodeFormatter): string | undefined {
        fmt.indentPush();

        let prec: string[] = [];
        if(this.preconditions.length !== 0) {
            prec = this.preconditions.map((pc) => fmt.indent(pc.emit(fmt)));
        }

        let postc: string[] = [];
        if(this.postconditions.length !== 0) {
            postc = this.postconditions.map((pc) => fmt.indent(pc.emit(fmt)));
        }

        let configs: string[] = [];
        if(this.configs !== undefined) {
            configs = [fmt.indent(`configs { ${this.configs.emit()} }`)];
        }

        let status: string[] = [];
        if(this.statusinfo.length !== 0) {
            status = [fmt.indent(`status ${this.statusinfo.map((so) => so.emit()).join(" | ")};`)];
        }

        let resources: string[] = [];
        if(this.resourcereqs.pathglobs.length !== 0) {
            const rrs = this.resourcereqs.pathglobs.map((rr) => ResourceInformation.emitSingleRInfo(fmt, rr.pg, rr.optas));
            resources = [fmt.indent(`resource { ${rrs.join(", ")} }`)];
        }
        
        let evs: string[] = [];
        if(this.envreqs.length !== 0) {
            const vvl = this.envreqs.map((ev) => ev.emit(fmt));
            evs = [fmt.indent(`env { ${vvl.join(", ")} }`)];
        }

        fmt.indentPop();
        if(prec.length === 0 && postc.length === 0 && status.length === 0 && evs.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc, ...configs, ...status, ...evs, ...resources].join("\n");
        }
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        const params = this.params.map((p) => p.emit(fmt)).join(", ");
        const result = this.resultType.emit();

        const minfo = this.emitMetaInfo(fmt);
        return `${attrs}api ${this.name}(${params}): ${result}${this.eventType !== undefined ? ", " + this.eventType.emit() : ""} ${this.body.emit(fmt, minfo)}`;
    }
}

class AgentDecl extends AbstractCoreDecl {
    readonly params: InvokeParameterDecl[];    
    readonly resultType: TypeSignature | undefined; //This may be set on a per call-site basis
    readonly eventType: TypeSignature | undefined;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly configs: TaskConfiguration;

    readonly statusinfo: TypeSignature[];
    readonly envreqs: EnvironmentVariableInformation[];
    readonly resourcereqs: ResourceInformation;

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: InvokeParameterDecl[], resultType: TypeSignature | undefined, eventType: TypeSignature | undefined, preconds: PreConditionDecl[], postconds: PostConditionDecl[], configs: TaskConfiguration, statusinfo: TypeSignature[], envreqs: EnvironmentVariableInformation[], resourcereqs: ResourceInformation, body: BodyImplementation) {
        super(file, sinfo, attributes, name);

        this.params = params;
        this.resultType = resultType;
        this.eventType = eventType;

        this.preconditions = preconds;
        this.postconditions = postconds

        this.configs = configs;

        this.statusinfo = statusinfo;
        this.envreqs = envreqs;
        this.resourcereqs = resourcereqs;

        this.body = body;
    }

    emitMetaInfo(fmt: CodeFormatter): string | undefined {
        fmt.indentPush();

        let prec: string[] = [];
        if(this.preconditions.length !== 0) {
            prec = this.preconditions.map((pc) => fmt.indent(pc.emit(fmt)));
        }

        let postc: string[] = [];
        if(this.postconditions.length !== 0) {
            postc = this.postconditions.map((pc) => fmt.indent(pc.emit(fmt)));
        }

        let configs: string[] = [];
        if(this.configs !== undefined) {
            configs = [fmt.indent(`configs { ${this.configs.emit()} }`)];
        }

        let status: string[] = [];
        if(this.statusinfo.length !== 0) {
            status = [fmt.indent(`status ${this.statusinfo.map((so) => so.emit()).join(" | ")};`)];
        }

        let resources: string[] = [];
        if(this.resourcereqs.pathglobs.length !== 0) {
            const rrs = this.resourcereqs.pathglobs.map((rr) => ResourceInformation.emitSingleRInfo(fmt, rr.pg, rr.optas));
            resources = [fmt.indent(`resource { ${rrs.join(", ")} }`)];
        }
        
        let evs: string[] = [];
        if(this.envreqs.length !== 0) {
            const vvl = this.envreqs.map((ev) => ev.emit(fmt));
            evs = [fmt.indent(`env{ ${vvl.join(", ")} }`)];
        }

        fmt.indentPop();
        if(prec.length === 0 && postc.length === 0 && status.length === 0 && evs.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc, ...configs, ...status, ...evs, ...resources].join("\n");
        }
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        const params = this.params.map((p) => p.emit(fmt)).join(", ");
        const iresult = this.resultType === undefined ? "<T>" : "";
        const eresult = this.resultType !== undefined ? (": " + this.resultType.emit()) : "";
        const eevent = this.eventType !== undefined ? (this.resultType !== undefined ? ", " : " ") + this.eventType.emit() : "";

        const minfo = this.emitMetaInfo(fmt);
        return `${attrs}agent ${this.name}${iresult}(${params})${eresult}${eevent} ${this.body.emit(fmt, minfo)}`;
    }
}

class TaskDecl extends AbstractNominalTypeDecl {
    readonly fields: MemberFieldDecl[] = [];
    readonly selfmethods: TaskMethodDecl[] = [];
    readonly actions: TaskActionDecl[] = [];

    readonly configs: TaskConfiguration = new TaskConfiguration(undefined, undefined, undefined);

    readonly statusinfo: TypeSignature[] = [];
    readonly envreqs: EnvironmentVariableInformation[] = [];
    readonly resourcereqs: ResourceInformation = new ResourceInformation([]);
    readonly eventinfo: TypeSignature[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string) {
        super(file, sinfo, attributes, ns, name, AdditionalTypeDeclTag.Std);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const mg: string[][] = [];
        
        const confstr = this.configs.emit();
        if(confstr !== undefined) {
            mg.push([fmt.indent(`configs { ${confstr} }`)]);
        }

        if(this.statusinfo.length !== 0) {
            mg.push([fmt.indent(`status ${this.statusinfo.map((so) => so.emit()).join(" | ")};`)]);
        }

        if(this.resourcereqs.pathglobs.length !== 0) {
            const rrs = this.resourcereqs.pathglobs.map((rr) => ResourceInformation.emitSingleRInfo(fmt, rr.pg, rr.optas));
            mg.push([fmt.indent(`resource { ${rrs.join(", ")} }`)]);
        }
        
        if(this.envreqs.length !== 0) {
            const vvl = this.envreqs.map((ev) => ev.emit(fmt));
            mg.push([fmt.indent(`env{ ${vvl.join(", ")} }`)]);
        }

        if(this.eventinfo.length !== 0) {
            mg.push([fmt.indent(`event ${this.eventinfo.map((et) => et.emit()).join(" | ")};`)]);
        }

        if(this.fields.length !== 0) {
            mg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        if(this.selfmethods.length !== 0) {
            mg.push(this.selfmethods.map((sm) => sm.emit(fmt)));
        }
        if(this.actions.length !== 0) {
            mg.push(this.actions.map((act) => act.emit(fmt)));
        }
        fmt.indentPop();

        let rootdecl = attrs + "task " + this.name + this.emitTerms(); 

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        let etail = "";
        if(bg.length !== 0) {
            etail = " {\n" + this.joinBodyGroups([...mg, ...bg]) + fmt.indent("\n}");
        }

        return `${rootdecl}${etail}`;
    }
}

class NamespaceConstDecl extends AbstractCoreDecl {
    readonly declaredType: TypeSignature;
    readonly value: Expression;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, value: Expression) {
        super(file, sinfo, attributes, name);

        this.declaredType = dtype;
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        const attr = this.attributes.length !== 0 ? this.attributes.map((a) => a.emit()).join(" ") + " " : "";
        return `${attr}const ${this.name}: ${this.declaredType.emit()} = ${this.value.emit(true, fmt)};`;
    }
}

class NamespaceUsing {
    readonly file: string;

    //
    //TODO: want to add a module/package scope component here too!!
    //
    readonly fromns: string;
    readonly asns: string | undefined;

    constructor(file: string, fromns: string, asns: string | undefined) {
        this.file = file;

        this.fromns = fromns;
        this.asns = asns;
    }

    emit(): string {
        if(this.asns === undefined) {
            return `using ${this.fromns};`;
        }
        else {
            return `using ${this.fromns} as ${this.asns};`;
        }
    }
}

type NSRegexNameInfo = {
    inns: string,
    nsmappings: [string, string][]
}

type NSRegexREInfoEntry = {
    name: string,
    restr: string
}

type NSRegexInfo = {
    nsinfo: NSRegexNameInfo,
    reinfos: NSRegexREInfoEntry[]
}

class NamespaceDeclaration {
    readonly name: string; 
    readonly topnamespace: string;
    readonly fullnamespace: FullyQualifiedNamespace;

    usings: NamespaceUsing[] = [];
    declaredNames: Set<string> = new Set<string>();
    declaredTypeNames: {name: string, hasterms: boolean}[] = []; //types, typedecls, tasks, agents
    declaredSubNSNames: Set<string> = new Set<string>();
    declaredConstNames: Set<string> = new Set<string>(); 
    declaredFunctionNames: Set<string> = new Set<string>();
    declaredAPINames: Set<string> = new Set<string>();
    declaredAgentNames: Set<string> = new Set<string>();

    subns: NamespaceDeclaration[] = [];

    consts: NamespaceConstDecl[] = [];
    functions: NamespaceFunctionDecl[] = []; //function as name+TemplateFlag+refFlag+lambdaFlag
    typedecls: AbstractNominalTypeDecl[] = [];

    apis: APIDecl[] = [];
    tasks: TaskDecl[] = [];
    agents: AgentDecl[] = [];

    constructor(name: string, topnamespace: string, fullnamespace: FullyQualifiedNamespace) {
        this.name = name;
        this.topnamespace = topnamespace;
        this.fullnamespace = fullnamespace;
    }

    isTopNamespace(): boolean {
        return this.name === this.topnamespace;
    }

    checkDeclNameClashNS(rname: string): boolean {
        if(!this.declaredNames.has(rname)) {
            return false;
        }

        //namespace always clashes with other namespaces and with simple member names
        if(this.declaredSubNSNames.has(rname) || this.declaredConstNames.has(rname) || this.declaredFunctionNames.has(rname) || this.declaredAPINames.has(rname)) {
            return true;
        }

        //we allow same names on types and subnamespaces IF the type has template terms
        return this.declaredTypeNames.find((tn) => tn.name === rname && tn.hasterms) !== undefined;
    }

    checkDeclNameClashType(rname: string, hasterms: boolean): boolean {
        if(!this.declaredNames.has(rname)) {
            return false;
        }

        //types always simple member names
        if(this.declaredConstNames.has(rname) || this.declaredFunctionNames.has(rname) || this.declaredAPINames.has(rname)) {
            return true;
        }

        //they also clash with each other even if they differ in templates
        if(this.declaredTypeNames.find((tn) => tn.name === rname) !== undefined) {
            return true;
        }

        //we allow same names on types and subnamespaces IF the type has template terms
        return !hasterms && this.declaredSubNSNames.has(rname);
    }

    checkDeclNameClashMemberSimple(rname: string): boolean {
        return this.declaredNames.has(rname);
    }

    emit(fmt: CodeFormatter): string {
        let res = "";

        if(this.isTopNamespace()) {
            res += `declare namespace ${this.name}`;
        
            fmt.indentPush();
            const usings = this.usings.map((u) => {
                res += fmt.indent(u.emit());
            });
            fmt.indentPop();

            if(this.usings.length === 0) {
                res += ";\n\n";
            }
            else {
                res += `{\n${usings.join("\n")}\n}\n\n`;
            }
        }
        else {
            res += `namespace ${this.name} {\n`;
            fmt.indentPush();
        }

        this.subns.forEach((ns) => {
            res += fmt.indent(ns.emit(fmt) + "\n");
        });
        if(this.subns.length !== 0) {
            res += "\n";
        }

        this.consts.forEach((c) => {
            res += fmt.indent(c.emit(fmt) + "\n");
        });
        if(this.consts.length !== 0) {
            res += "\n";
        }

        this.functions.forEach((f) => {
            res += fmt.indent(f.emit(fmt) + "\n");
        });
        if(this.functions.length !== 0) {
            res += "\n";
        }

        this.typedecls.forEach((td) => {
            res += fmt.indent(td.emit(fmt) + "\n");
        });
        if(this.typedecls.length !== 0) {
            res += "\n";
        }

        this.apis.forEach((a) => {
            res += fmt.indent(a.emit(fmt) + "\n");
        });
        if(this.apis.length !== 0) {
            res += "\n";
        }

        this.agents.forEach((a) => {
            res += fmt.indent(a.emit(fmt) + "\n");
        });
        if(this.agents.length !== 0) {
            res += "\n";
        }

        this.tasks.forEach((t) => {
            res += fmt.indent(t.emit(fmt) + "\n");
        });

        if(res.endsWith("\n\n")) {
            res = res.slice(0, res.length - 1);
        }

        if(!this.isTopNamespace()) {
            fmt.indentPop();
            res += fmt.indent("}\n");
        }

        return res;
    }
}

class Assembly {
    readonly toplevelNamespaces: NamespaceDeclaration[] = [];
    
    hasToplevelNamespace(ns: string): boolean {
        return this.toplevelNamespaces.find((nsd) => nsd.name === ns) !== undefined;
    }

    getCoreNamespace(): NamespaceDeclaration {
        return this.toplevelNamespaces.find((nsd) => nsd.name === "Core") as NamespaceDeclaration;
    }

    getToplevelNamespace(ns: string): NamespaceDeclaration | undefined {
        return this.toplevelNamespaces.find((nsd) => nsd.name === ns);
    }

    ensureToplevelNamespace(ns: string): NamespaceDeclaration {
        if (!this.hasToplevelNamespace(ns)) {
            this.toplevelNamespaces.push(new NamespaceDeclaration(ns, ns, new FullyQualifiedNamespace([ns])));
        }

        return this.getToplevelNamespace(ns) as NamespaceDeclaration;
    }

    resolveNamespaceDecl(ns: string[]): NamespaceDeclaration | undefined {
        let curns = this.getToplevelNamespace(ns[0]);
        if(curns === undefined) {
            return undefined;
        }

        for(let i = 1; i < ns.length; ++i) {
            curns = curns.subns.find((nns) => nns.name === ns[i]);
            if(curns === undefined) {
                return undefined;
            }
        }

        return curns;
    }

    resolveConstantRegexExpressionValue(exp: LiteralRegexExpression | AccessNamespaceConstantExpression, inns: string): [string | undefined, string] {
        if(exp instanceof LiteralRegexExpression) {
            return [exp.value, inns];
        }
        else {
            const nsconst = this.resolveNamespaceConstant(exp.ns, exp.name);
            if(nsconst === undefined) {
                return [undefined, inns];
            }

            const nnins = exp.ns.emit();
            if(nsconst.value instanceof LiteralRegexExpression) {
                return [nsconst.value.value, nnins];
            }
            else if(nsconst.value instanceof AccessNamespaceConstantExpression) {
                return this.resolveConstantRegexExpressionValue(nsconst.value, nnins);
            }
            else {
                return [undefined, inns];
            }
        }
    }

    resolveValidatorLiteral(exp: Expression): Expression | undefined {
        if(exp.tag === ExpressionTag.AccessNamespaceConstantExpression) {
            const cexp = exp as AccessNamespaceConstantExpression;
            const nsconst = this.resolveNamespaceConstant(cexp.ns, cexp.name);
            if(nsconst === undefined) {
                return undefined;
            }

            return this.resolveValidatorLiteral(nsconst.value);
        }
        else {
            if(exp.tag === ExpressionTag.LiteralUnicodeRegexExpression || exp.tag === ExpressionTag.LiteralCRegexExpression || exp.tag === ExpressionTag.LiteralGlobExpression) {
                return exp;
            }
            else {
                return undefined;
            }
        }
    }

    static checkFunctionSigMatch(fd1: FunctionInvokeDecl, fd2: FunctionInvokeDecl): boolean {
        if(fd1.name !== fd2.name) {
            return false;
        }

        if((fd1.terms.length !== 0) !== (fd2.terms.length !== 0)) {
            return false;
        }

        const l1has = fd1.params.some((p) => p.type instanceof LambdaTypeSignature);
        const l2has = fd2.params.some((p) => p.type instanceof LambdaTypeSignature);
        if(l1has !== l2has) {
            return false;
        }

        const r1isref = fd1.params.some((p) => p.pkind !== undefined);
        const r2isref = fd2.params.some((p) => p.pkind !== undefined);
        if(r1isref !== r2isref) {
            return false;
        }

        return true;
    }

    static checkMethodSigMatch(md1: MethodDecl, md2: MethodDecl): boolean {
        if(md1.name !== md2.name) {
            return false;
        }

        if((md1.terms.length !== 0) !== (md2.terms.length !== 0)) {
            return false;
        }

        const l1has = md1.params.some((p) => p.type instanceof LambdaTypeSignature);
        const l2has = md2.params.some((p) => p.type instanceof LambdaTypeSignature);
        if(l1has !== l2has) {
            return false;
        }

        const r1isref = md1.params.some((p) => p.pkind !== undefined);
        const r2isref = md2.params.some((p) => p.pkind !== undefined);
        if((r1isref || md1.isThisRef) !== (r2isref || md2.isThisRef)) {
            return false;
        }

        return true;
    }

    static resolveSigMatch(s1: {name: string, isTemplate: boolean, hasLambda: boolean, isRef: boolean}, s2: {name: string, isTemplate: boolean, hasLambda: boolean, isRef: boolean}): boolean {
        if(s1.name !== s2.name) {
            return false;
        }

        if(s1.isTemplate !== s2.isTemplate) {
            return false;
        }
        
        if(s1.hasLambda !== s2.hasLambda) {
            return false;
        }

        if(s1.isRef !== s2.isRef) {
            return false;
        }
        
        return true;
    }

    resolveNamespaceConstant(ns: FullyQualifiedNamespace, name: string): NamespaceConstDecl | undefined {
        const nsdecl = this.resolveNamespaceDecl(ns.ns);
        if(nsdecl === undefined) {
            return undefined;
        }

        return nsdecl.consts.find((c) => c.name === name);
    }

    resolveNamespaceFunction(ns: FullyQualifiedNamespace, name: string, isTemplate: boolean, hasLambda: boolean, isRef: boolean): NamespaceFunctionDecl | undefined {
        const nsdecl = this.resolveNamespaceDecl(ns.ns);
        if(nsdecl === undefined) {
            return undefined;
        }

        const fnsig = {name: name, isTemplate: isTemplate, hasLambda: hasLambda, isRef: isRef};
        return nsdecl.functions.find((c) => Assembly.resolveSigMatch(fnsig, {name: c.name, isTemplate: c.terms.length !== 0, hasLambda: c.params.some((p) => p.type instanceof LambdaTypeSignature), isRef: c.params.some((p) => p.pkind !== undefined)}));
    }

    tryReduceConstantExpressionToRE(exp: Expression): LiteralRegexExpression | undefined {
        if(exp instanceof LiteralRegexExpression) {
            return exp;
        }
        else if (exp instanceof AccessNamespaceConstantExpression) {
            const nsresl = this.resolveNamespaceConstant(exp.ns, exp.name);
            if(nsresl === undefined) {
                return undefined;
            }

            return this.tryReduceConstantExpressionToRE(nsresl.value);
        }
        else {
            return undefined;
        }
    }

    loadConstantsAndValidatorREs(nsdecl: NamespaceDeclaration): NSRegexInfo[] {
        const inns = nsdecl.fullnamespace.ns.join("::");
        const nsmappings = nsdecl.usings.filter((u) => u.asns !== undefined).map((u) => [u.fromns, u.asns as string] as [string, string]);
        const nsinfo: NSRegexNameInfo = {inns: inns, nsmappings: nsmappings};

        const reinfos: NSRegexREInfoEntry[] = [];
        nsdecl.consts.forEach((c) => {
            const re = this.tryReduceConstantExpressionToRE(c.value);
            if(re !== undefined) {
                reinfos.push({name: c.name, restr: re.value});
            }
        });

        const subnsinfo = nsdecl.subns.flatMap((ns) => this.loadConstantsAndValidatorREs(ns));

        return [{nsinfo: nsinfo, reinfos: reinfos}, ...subnsinfo].filter((nsi) => nsi.reinfos.length !== 0);
    }
}

export {
    MIN_SAFE_INT, MAX_SAFE_INT, MAX_SAFE_NAT, MIN_SAFE_CHK_INT, MAX_SAFE_CHK_INT, MAX_SAFE_CHK_NAT,
    WELL_KNOWN_RETURN_VAR_NAME, WELL_KNOWN_EVENTS_VAR_NAME,
    TemplateTermDeclExtraTag, TemplateTermDecl, TypeTemplateTermDecl, InvokeTemplateTermDecl, InvokeTemplateTypeRestrictionClause, InvokeTemplateTypeRestriction, 
    TaskConfiguration,
    AbstractDecl, 
    ConditionDecl, PreConditionDecl, PostConditionDecl, InvariantDecl, ValidateDecl,
    DeclarationAttibute, AbstractCoreDecl,
    InvokeParameterDecl, AbstractInvokeDecl, 
    LambdaDecl,
    ExplicitInvokeDecl,
    TestAssociation,
    FunctionInvokeDecl, NamespaceFunctionDecl, TypeFunctionDecl,
    MethodDecl, TaskMethodDecl, TaskActionDecl,
    ConstMemberDecl, MemberFieldDecl,
    AbstractNominalTypeDecl, AdditionalTypeDeclTag,
    EnumTypeDecl,
    TypedeclTypeDecl,
    AbstractEntityTypeDecl, PrimitiveEntityTypeDecl,
    InternalEntityTypeDecl,
    ConstructableTypeDecl, OkTypeDecl, FailTypeDecl, APIErrorTypeDecl, APIRejectedTypeDecl, APIDeniedTypeDecl, APIFlaggedTypeDecl, APISuccessTypeDecl, SomeTypeDecl, MapEntryTypeDecl,
    AbstractCollectionTypeDecl, ListTypeDecl, StackTypeDecl, QueueTypeDecl, SetTypeDecl, MapTypeDecl,
    EventListTypeDecl,
    EntityTypeDecl, 
    AbstractConceptTypeDecl, InternalConceptTypeDecl, 
    OptionTypeDecl, ResultTypeDecl, APIResultTypeDecl,
    ConceptTypeDecl, 
    DatatypeMemberEntityTypeDecl, DatatypeTypeDecl,
    EnvironmentVariableInformation, ResourceInformation, 
    APIDecl, AgentDecl,
    TaskDecl,
    NamespaceConstDecl, NamespaceUsing, NamespaceDeclaration,
    NSRegexInfo, NSRegexNameInfo, NSRegexREInfoEntry,
    Assembly
};
