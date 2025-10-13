
import { FullyQualifiedNamespace, TypeSignature, LambdaTypeSignature, RecursiveAnnotation, TemplateTypeSignature, VoidTypeSignature, LambdaParameterSignature, AutoTypeSignature, NominalTypeSignature } from "./type.js";
import { Expression, BodyImplementation, ExpressionTag, AccessNamespaceConstantExpression, LiteralRegexExpression, ChkLogicExpression } from "./body.js";

import { BuildLevel, CodeFormatter, SourceInfo } from "./build_decls.js";

const MIN_SAFE_INT = -4611686018427387903n;
const MAX_SAFE_INT = 4611686018427387903n;

//negation and conversion are always safe
const MAX_SAFE_NAT = 4611686018427387903n;

const WELL_KNOWN_RETURN_VAR_NAME = "$return";
const WELL_KNOWN_EVENTS_VAR_NAME = "$events";
const WELL_KNOWN_SRC_VAR_NAME = "$src";

enum TemplateTermDeclExtraTag {
    KeyType = "keytype",
    Numeric = "numeric"
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
    isSpecialAPIResultEntity(): boolean { return (this instanceof APIRejectedTypeDecl) || (this instanceof APIFailedTypeDecl) || (this instanceof APIErrorTypeDecl) || (this instanceof APISuccessTypeDecl); }

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
    optofexp: Expression | undefined;

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

class APIFailedTypeDecl extends ConstructableTypeDecl {
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

class CRopeTypeDecl extends AbstractCollectionTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class CRopeIteratorTypeDecl extends InternalEntityTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    // Internal to the cpp runtime so no need to emit anything
    emit(fmt: CodeFormatter): string {
        return "";
    }
}

class UnicodeRopeTypeDecl extends AbstractCollectionTypeDecl {
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
    readonly nestedEntityDecls: (APIErrorTypeDecl | APIFailedTypeDecl | APIRejectedTypeDecl | APISuccessTypeDecl)[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    getAPIErrorType(): APIErrorTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof APIErrorTypeDecl) as APIErrorTypeDecl;
    }

    getAPIFailedType(): APIFailedTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof APIFailedTypeDecl) as APIFailedTypeDecl;
    }

    getAPIRejectedType(): APIRejectedTypeDecl {
        return this.nestedEntityDecls.find((ned) => ned instanceof APIRejectedTypeDecl) as APIRejectedTypeDecl;
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
    readonly evname: string; //cstring
    readonly evtype: TypeSignature;
    readonly optdefault: Expression | undefined;

    constructor(evname: string, evtype: TypeSignature, optdefault: Expression | undefined) {
        this.evname = evname;
        this.evtype = evtype;
        this.optdefault = optdefault;
    }

    emit(fmt: CodeFormatter): string {
        if(this.optdefault === undefined) {
            return fmt.indent(`${this.evname}: ${this.evtype.emit()}`);
        }
        else {
            return fmt.indent(`${this.evname}: ${this.evtype.emit()} = ${this.optdefault.emit(true, fmt)}`);
        }
    }
}

////
//  This is copied from BREX path_glob.h for reference here -- see how it works with the access modes
//
//  /x/y/*     <-- all files that are single extensions of the prefix
//  /x/y/*/    <-- all directories that are single extensions of the prefix
//
//  /x/y/**   <-- all files that are extensions of the prefix
//  /x/y/**/  <-- all directories that are extensions of the prefix
//  
//  /x/y/*.*     <-- all files that have an extension with a file extension
//  /x/y/**/*.*  <-- all files that are an extension of the prefix and with a file extension
//

//Are all of these in effect idempotent???
enum ResourceAccessModes {
    get    = "?",  //no side effects and -- reads the value or list (elements) 
    modify = "!",  //replaces an existing value
    create = "+",  //creates a new value or list (that did not previously exist)
    delete = "-",  //removes a value or list that may have previously existed
    any =    "*"   //any possible of the above
}

class ResourceInformation {
    readonly pathglob: Expression; //this is g\xxxx\* or g\xxxx\oftype or g\xxxx\_oftype, or constant, or an environment variable
    readonly accessInfo: ResourceAccessModes[];

    constructor(pathglob: Expression, accessInfo: ResourceAccessModes[]) {
        this.pathglob = pathglob;
        this.accessInfo = accessInfo;
    }

    emit(fmt: CodeFormatter): string {
        const mstr = this.accessInfo.join("");
        return fmt.indent(`${this.pathglob.emit(true, fmt)}@[${mstr}]`);
    }
}

class APIDecl extends AbstractCoreDecl {
    readonly params: InvokeParameterDecl[];    
    readonly resultType: TypeSignature;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly statusOutputs: TypeSignature[];
    readonly envVarRequirements: EnvironmentVariableInformation[];
    readonly resourceImpacts: ResourceInformation[] | "**" | "{}";

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: InvokeParameterDecl[], resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], statusOutputs: TypeSignature[], envVarRequirements: EnvironmentVariableInformation[], resourceImpacts: ResourceInformation[] | "**" | "{}", body: BodyImplementation) {
        super(file, sinfo, attributes, name);
        
        this.params = params;
        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds

        this.statusOutputs = statusOutputs;
        this.envVarRequirements = envVarRequirements;
        this.resourceImpacts = resourceImpacts;

        this.body = body;
    }

    emitMetaInfo(fmt: CodeFormatter): string | undefined {
        fmt.indentPush();

        let prec: string[] = [];
        if(this.preconditions.length !== 0) {
            prec = this.preconditions.map((pc) => pc.emit(fmt));
        }

        let postc: string[] = [];
        if(this.postconditions.length !== 0) {
            postc = this.postconditions.map((pc) => pc.emit(fmt));
        }

        let status: string[] = [];
        if(this.statusOutputs.length !== 0) {
            status = [`status {${this.statusOutputs.map((so) => so.emit()).join(", ")}}`];
        }

        let resources: string[] = [];
        if(this.resourceImpacts === "**") {
            resources = ["resource { ** }"];
        }
        else if(this.resourceImpacts === "{}") {
            resources = ["resource { }"];
        }
        else {
            resources = [`resource { ${this.resourceImpacts.map((ri) => ri.emit(fmt)).join(", ")} }`];
        }

        const vvl = this.envVarRequirements.map((ev) => ev.emit(fmt));

        fmt.indentPush();
        const vvs = [vvl[0], ...vvl.slice(1).map((vv) => fmt.indent(vv))].join("\n");
        fmt.indentPop();

        const evs = [`env{ ${vvs} ${fmt.indent("}")}`];
        
        fmt.indentPop();
        if(prec.length === 0 && postc.length === 0 && status.length === 0 && evs.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc, ...status, ...evs, ...resources].join("\n");
        }
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        const params = this.params.map((p) => p.emit(fmt)).join(", ");
        const result = this.resultType.emit();

        const minfo = this.emitMetaInfo(fmt);
        return `${attrs}api ${this.name}(${params}): ${result} ${this.body.emit(fmt, minfo)}`;
    }
}

class TaskDecl extends AbstractNominalTypeDecl {
    readonly fields: MemberFieldDecl[] = [];
    readonly selfmethods: TaskMethodDecl[] = [];
    readonly actions: TaskActionDecl[] = [];

    eventsInfo: TypeSignature | undefined; //undefined means no events
    statusInfo: TypeSignature[] | undefined; //undefined means no status
    envVarRequirementInfo: EnvironmentVariableInformation[] | undefined; 
    resourceImpactInfo: ResourceInformation[] | "**" | "{}" | "?" | undefined; //** means any possible resource impact -- ? means passthrough
    
    //If this is defined then the info is all taken from the API
    implementsapi: [FullyQualifiedNamespace, string] | undefined = undefined;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string) {
        super(file, sinfo, attributes, ns, name, AdditionalTypeDeclTag.Std);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const mg: string[][] = [];
        if(this.eventsInfo !== undefined) {
            mg.push([`event ${this.eventsInfo.emit()}`]);
        }
        if(this.statusInfo !== undefined) {
            mg.push([`status {${this.statusInfo.map((so) => so.emit()).join(", ")}}`]);
        }
        if(this.envVarRequirementInfo !== undefined) {
            const vvl = this.envVarRequirementInfo.map((ev) => ev.emit(fmt));

            fmt.indentPush();
            const vvs = [vvl[0], ...vvl.slice(1).map((vv) => fmt.indent(vv))].join("\n");
            fmt.indentPop();

            mg.push([`env{ ${vvs} ${fmt.indent("}")}`]);
        }
        if(this.resourceImpactInfo !== undefined) {
            if(this.resourceImpactInfo === "**") {
                mg.push(["resource { ** }"]);
            }
            else if(this.resourceImpactInfo === "{}") {
                mg.push(["resource { }"]);
            }
            else if(this.resourceImpactInfo === "?") {
                mg.push(["resource { ? }"]);
            }
            else {
                mg.push([`resource { ${this.resourceImpactInfo.map((ri) => ri.emit(fmt)).join(", ")} }`]);
            }
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
        if(this.implementsapi !== undefined) {
            rootdecl += `implements ${this.implementsapi[0].emit()}::${this.implementsapi[1]}`;
        }

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        let etail = "";
        if(bg.length !== 0) {
            etail = " {\n" + this.joinBodyGroups([...bg, ...mg]) + fmt.indent("\n}");
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
    declaredTypeNames: {name: string, hasterms: boolean}[] = []; //types, typedecls, and tasks
    declaredSubNSNames: Set<string> = new Set<string>();
    declaredConstNames: Set<string> = new Set<string>(); 
    declaredFunctionNames: Set<string> = new Set<string>(); //functions, apis, and consts
    declaredAPINames: Set<string> = new Set<string>(); //functions, apis, and consts

    subns: NamespaceDeclaration[] = [];

    consts: NamespaceConstDecl[] = [];
    functions: NamespaceFunctionDecl[] = [];
    typedecls: AbstractNominalTypeDecl[] = [];

    apis: APIDecl[] = [];
    tasks: TaskDecl[] = [];

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

    checkDeclNameClashMember(rname: string): boolean {
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

    resolveNamespaceConstant(ns: FullyQualifiedNamespace, name: string): NamespaceConstDecl | undefined {
        const nsdecl = this.resolveNamespaceDecl(ns.ns);
        if(nsdecl === undefined) {
            return undefined;
        }

        return nsdecl.consts.find((c) => c.name === name);
    }

    resolveNamespaceFunction(ns: FullyQualifiedNamespace, name: string): NamespaceFunctionDecl | undefined {
        const nsdecl = this.resolveNamespaceDecl(ns.ns);
        if(nsdecl === undefined) {
            return undefined;
        }

        return nsdecl.functions.find((c) => c.name === name);
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
    MIN_SAFE_INT, MAX_SAFE_INT, MAX_SAFE_NAT,
    WELL_KNOWN_RETURN_VAR_NAME, WELL_KNOWN_EVENTS_VAR_NAME, WELL_KNOWN_SRC_VAR_NAME,
    TemplateTermDeclExtraTag, TemplateTermDecl, TypeTemplateTermDecl, InvokeTemplateTermDecl, InvokeTemplateTypeRestrictionClause, InvokeTemplateTypeRestriction, 
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
    InternalEntityTypeDecl, CRopeIteratorTypeDecl,
    ConstructableTypeDecl, OkTypeDecl, FailTypeDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APISuccessTypeDecl, SomeTypeDecl, MapEntryTypeDecl,
    AbstractCollectionTypeDecl, ListTypeDecl, CRopeTypeDecl, UnicodeRopeTypeDecl, StackTypeDecl, QueueTypeDecl, SetTypeDecl, MapTypeDecl,
    EventListTypeDecl,
    EntityTypeDecl, 
    AbstractConceptTypeDecl, InternalConceptTypeDecl, 
    OptionTypeDecl, ResultTypeDecl, APIResultTypeDecl,
    ConceptTypeDecl, 
    DatatypeMemberEntityTypeDecl, DatatypeTypeDecl,
    EnvironmentVariableInformation, ResourceAccessModes, ResourceInformation, APIDecl,
    TaskDecl,
    NamespaceConstDecl, NamespaceUsing, NamespaceDeclaration,
    NSRegexInfo, NSRegexNameInfo, NSRegexREInfoEntry,
    Assembly
};
