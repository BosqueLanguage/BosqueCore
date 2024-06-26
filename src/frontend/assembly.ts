
import { FullyQualifiedNamespace, TypeSignature, LambdaTypeSignature, RecursiveAnnotation, TemplateTypeSignature, VoidTypeSignature, LambdaParameterSignature, AutoTypeSignature } from "./type.js";
import { Expression, BodyImplementation, ConstantExpressionValue } from "./body.js";

import { BuildLevel, CodeFormatter, SourceInfo } from "./build_decls.js";

const WELL_KNOWN_RETURN_VAR_NAME = "$return";
const WELL_KNOWN_EVENTS_VAR_NAME = "$events";
const WELL_KNOWN_SRC_VAR_NAME = "$src";

enum TemplateTermDeclExtraTag {
    None,
    Unique
}

class TemplateTermDecl {
    readonly name: string;
    readonly tconstraint: TypeSignature;
    readonly extraTags: TemplateTermDeclExtraTag[];

    constructor(name: string, tconstraint: TypeSignature, extraTags: TemplateTermDeclExtraTag[]) {
        this.name = name;
        this.tconstraint = tconstraint;
        this.extraTags = extraTags;
    }

    emitHelper(isinferable: boolean): string {
        let ttgs: string[] = [];
        if(this.extraTags.includes(TemplateTermDeclExtraTag.Unique)) {
            ttgs.push("unique");
        }

        let tstr = (this.tconstraint.tkeystr !== "Any") ? `: ${this.tconstraint.tkeystr}` : "";

        return `${this.name}${isinferable ? "?" : ""}: ${[...ttgs, tstr].join(" ")}`;
    }
}

class TypeTemplateTermDecl extends TemplateTermDecl {
    constructor(name: string, tags: TemplateTermDeclExtraTag[], tconstraint: TypeSignature) {
        super(name, tconstraint, tags);
    }

    emit(): string {
        return this.emitHelper(false);
    }
}

class InvokeTemplateTermDecl extends TemplateTermDecl {
    readonly isinferable: boolean;

    constructor(name: string, tags: TemplateTermDeclExtraTag[], tconstraint: TypeSignature, isinferable: boolean) {
        super(name, tconstraint, tags);
        this.isinferable = isinferable;
    }

    emit(): string {
        return this.emitHelper(this.isinferable);
    }
}

abstract class InvokeTemplateTypeRestrictionClause {
    abstract emit(): string ;
}

class InvokeTemplateTypeRestrictionClauseUnify extends InvokeTemplateTypeRestrictionClause {
    readonly vname: string;
    readonly unifyinto: TypeSignature;

    constructor(vname: string, unifyinto: TypeSignature) {
        super();
        this.vname = vname;
        this.unifyinto = unifyinto;
    }

    emit(): string {
        return `type(${this.vname}) -> ${this.unifyinto.tkeystr}`;
    }
}

class InvokeTemplateTypeRestrictionClauseSubtype extends InvokeTemplateTypeRestrictionClause {
    readonly t: TemplateTypeSignature;
    readonly subtype: TypeSignature;

    constructor(t: TemplateTypeSignature, subtype: TypeSignature) {
        super();
        this.t = t;
        this.subtype = subtype;
    }

    emit(): string {
        return `${this.t}@${this.subtype.tkeystr}`;
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
    readonly exp: Expression;

    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, level: BuildLevel, issoft: boolean, exp: Expression) {
        super(file, sinfo, tag);

        this.level = level;
        this.issoft = issoft;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("requires" + this.emitDiagnosticTag() + (this.issoft ? " softcheck" : "") + (this.level !== "release" ? (" " + this.level) : "") + " " + this.exp.emit(true, fmt) + ";");
    }
}

class PostConditionDecl extends ConditionDecl {
    readonly level: BuildLevel;
    readonly issoft: boolean;
    readonly exp: Expression;

    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, level: BuildLevel, issoft: boolean, exp: Expression) {
        super(file, sinfo, tag);

        this.level = level;
        this.issoft = issoft;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("ensures" + this.emitDiagnosticTag() + (this.issoft ? " softcheck" : "") + (this.level !== "release" ? (" " + this.level) : "") + " " + this.exp.emit(true, fmt) + ";");
    }
}

class InvariantDecl extends ConditionDecl {
    readonly level: BuildLevel;
    readonly exp: ConstantExpressionValue;

    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, level: BuildLevel, exp: ConstantExpressionValue) {
        super(file, sinfo, tag);

        this.level = level;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("invariant" + this.emitDiagnosticTag() + (this.level !== "release" ? (" " + this.level) : "") + " " + this.exp.emit(true, fmt) + ";");
    }
}

class ValidateDecl extends ConditionDecl {
    readonly exp: ConstantExpressionValue;

    constructor(file: string, sinfo: SourceInfo, tag: string | undefined, exp: ConstantExpressionValue) {
        super(file, sinfo, tag);

        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("validate" + this.emitDiagnosticTag() + " " + this.exp.emit(true, fmt) + ";");
    }
}

enum InvokeExampleKind {
    Std,
    Test,
    Spec
}

abstract class InvokeExample extends AbstractDecl {
    readonly kind: InvokeExampleKind;

    constructor(file: string, sinfo: SourceInfo, ekind: InvokeExampleKind) {
        super(file, sinfo);
        this.kind = ekind;
    }
}

class InvokeExampleDeclInline extends InvokeExample {
    readonly entries: {args: Expression[], output: Expression}[];

    constructor(file: string, sinfo: SourceInfo, ekind: InvokeExampleKind, entries: {args: Expression[], output: Expression}[]) {
        super(file, sinfo, ekind);
        this.entries = entries;
    }

    emit(fmt: CodeFormatter): string {
        const estr = this.entries.map((e) => `(${e.args.map((a) => a.emit(true, fmt)).join(", ")}) => ${e.output.emit(true, fmt)}`).join("; ");

        if(this.kind === InvokeExampleKind.Spec) {
            return fmt.indent(`spec { ${estr} }`);
        }
        else if(this.kind === InvokeExampleKind.Test) {
            return fmt.indent(`test { ${estr} }`);
        }
        else {
            return fmt.indent(`example { ${estr} }`);
        }
    }
}

class InvokeExampleDeclFile extends InvokeExample {
    readonly filepath: string; //may use the ROOT and SRC environment variables

    constructor(file: string, sinfo: SourceInfo, ekind: InvokeExampleKind, filepath: string) {
        super(file, sinfo, ekind);
        this.filepath = filepath;
    }

    emit(fmt: CodeFormatter): string {
        if(this.kind === InvokeExampleKind.Test) {
            return fmt.indent(`test ${this.filepath};`);
        }
        else {
            return fmt.indent(`example ${this.filepath};`);
        }
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
        if(this.text === undefined) {
            return `%** ${this.text} **%`;
        }
        else {
            return `${this.name}${this.tags.length === 0 ? "" : " [" + this.tags.map((t) => `${t.enumType.tkeystr}::${t.tag}`).join(", ") + "]"}`;
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
    readonly optDefaultValue: ConstantExpressionValue | undefined;
    readonly isRefParam: boolean;
    readonly isRestParam: boolean;

    constructor(name: string, type: TypeSignature, optDefaultValue: ConstantExpressionValue | undefined, isRefParam: boolean, isRestParam: boolean) {
        this.name = name;
        this.type = type;
        this.optDefaultValue = optDefaultValue;
        this.isRefParam = isRefParam;
        this.isRestParam = isRestParam;
    }

    emit(fmt: CodeFormatter): string {
        const tdecl = this.type instanceof AutoTypeSignature ? "" : `: ${this.type.tkeystr}`;
        const defv = this.optDefaultValue === undefined ? "" : ` = ${this.optDefaultValue.emit(true, fmt)}`;
        return `${(this.isRefParam ? "ref " : "")}${this.isRestParam ? "..." : ""}${this.name}${tdecl}${defv}`;
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
        let result = (this.resultType instanceof VoidTypeSignature) ? "" : (": " + this.resultType.tkeystr);

        return [`${attrs}${rec}`, `(${params})${result}`];
    }
}

class LambdaDecl extends AbstractInvokeDecl {
    readonly captureVarSet: Set<string>;

    readonly isAuto: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: "fn" | "pred", recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, captureVarSet: Set<string>, isAuto: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body);

        this.captureVarSet = captureVarSet;
        this.isAuto = isAuto;
    }

    generateSig(sinfo: SourceInfo): TypeSignature {
        const lpsigs = this.params.map((p) => new LambdaParameterSignature(p.type, p.isRefParam, p.isRestParam));
        return new LambdaTypeSignature(sinfo, this.recursive, this.name as ("fn" | "pred"), lpsigs, this.resultType);
    }
    
    private emitCaptureInfo(): string {
        let capturev = "";
        if(this.captureVarSet.size !== 0) {
            capturev = "[" + Array.from(this.captureVarSet).sort().join(", ") + "]";
        }

        return "%*" + capturev + "*%";
    }

    emit(fmt: CodeFormatter): string {
        const ssig = this.emitSig(fmt);

        return `${ssig[0]}${this.name}${ssig[1]} ${this.body.emit(fmt, this.emitCaptureInfo())}`;
    }
}

abstract class ExplicitInvokeDecl extends AbstractInvokeDecl {
    readonly terms: InvokeTemplateTermDecl[];
    readonly termRestriction: InvokeTemplateTypeRestriction | undefined;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly examples: InvokeExample[];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[]) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body);

        this.terms = terms;
        this.termRestriction = termRestriction;

        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.examples = examples;
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

        let examples: string[] = [];
        if(this.examples.length !== 0) {
            examples = this.examples.map((ex) => ex.emit(fmt));
        }

        if(prec.length === 0 && postc.length === 0 && examples.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc, ...examples].join("\n");
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
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[]) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }
}

class NamespaceFunctionDecl extends FunctionInvokeDecl {
    readonly fkind: "function" | "predicate" | "errtest" | "chktest";

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[], fkind: "function" | "predicate" | "errtest" | "chktest") {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);

        this.fkind = fkind;
    }

    getDeclarationTag(): string {
        return this.fkind;
    }
}

class TypeFunctionDecl extends FunctionInvokeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[]) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }

    getDeclarationTag(): string {
        return "function";
    }
}

class MethodDecl extends ExplicitInvokeDecl {
    readonly isThisRef: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[], isThisRef: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);

        this.isThisRef = isThisRef;
    }

    getDeclarationTag(): string {
        return (this.isThisRef ? "ref " : "") + "method";
    }
}

class TaskMethodDecl extends ExplicitInvokeDecl {
    readonly isSelfRef: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[], isSelfRef: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);

        this.isSelfRef = isSelfRef;
    }

    getDeclarationTag(): string {
        return (this.isSelfRef ? "ref " : "") + "method";
    }
}

class TaskActionDecl extends ExplicitInvokeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: InvokeParameterDecl[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[]) {
        super(file, sinfo, attributes, name, "no", params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }

    getDeclarationTag(): string {
        return "action";
    }
}

class ConstMemberDecl extends AbstractCoreDecl {
    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
        super(file, sinfo, attributes, name);

        this.declaredType = dtype;
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}const ${this.name}: ${this.declaredType.tkeystr} = ${this.value.emit(true, fmt)};`);
    }
}

class MemberFieldDecl extends AbstractCoreDecl {
    readonly declaredType: TypeSignature;
    readonly defaultValue: ConstantExpressionValue | undefined;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, dvalue: ConstantExpressionValue | undefined) {
        super(file, sinfo, attributes, name);
        
        this.declaredType = dtype;
        this.defaultValue = dvalue;
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        if(this.defaultValue === undefined) {
            return fmt.indent(`${attrs}field ${this.name}: ${this.declaredType.tkeystr};`);
        }
        else {
            return fmt.indent(`${attrs}field ${this.name}: ${this.declaredType.tkeystr} = ${this.defaultValue.emit(true, fmt)};`);
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

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag) {
        super(file, sinfo);

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.etag = etag;
    }

    //These are our annoying nested types
    isSpecialResultEntity(): boolean { return (this instanceof OkTypeDecl) || (this instanceof ErrTypeDecl); }
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

    emitTerms(): string {
        return this.terms.length !== 0 ? ("<" + this.terms.map((tt) => tt.emit()).join(", ") + ">") : "";
    }

    emitProvides(): string {
        return this.provides.length !== 0 ? (" provides" + this.provides.map((p) => p.tkeystr).join(", ")) : "";
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

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, etag: AdditionalTypeDeclTag, valuetype: TypeSignature) {
        super(file, sinfo, attributes, ns, name, etag);

        this.valuetype = valuetype;
    }

    emit(fmt: CodeFormatter): string {
        const tdcl = `${this.emitAttributes()}${this.emitAdditionalTag()}typedecl ${this.name}${this.emitTerms()} = ${this.valuetype.tkeystr}`;

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        if(bg.length === 0 && this.provides.length === 1 && this.provides[0].tkeystr === "Some") {
            return tdcl + ";";
        }
        else {
            return tdcl + " &" + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
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

class RegexValidatorTypeDecl extends InternalEntityTypeDecl {
    readonly regex: string;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, regex: string) {
        super(file, sinfo, attributes, name);

        this.regex = regex;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}validator ${this.name} = ${this.regex};`);
    }
}

class CRegexValidatorTypeDecl extends InternalEntityTypeDecl {
    readonly regex: string;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, regex: string) {
        super(file, sinfo, attributes, name);

        this.regex = regex;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}validator ${this.name} = ${this.regex};`);
    }
}

class PathValidatorTypeDecl extends InternalEntityTypeDecl {
    readonly pathglob: string;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, pathglob: string) {
        super(file, sinfo, attributes, name);

        this.pathglob = pathglob;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}validator ${this.name} = ${this.pathglob};`);
    }
}

abstract class ThingOfTypeDecl extends InternalEntityTypeDecl {
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

class StringOfTypeDecl extends ThingOfTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class CStringOfTypeDecl extends ThingOfTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class PathOfTypeDecl extends ThingOfTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class PathFragmentOfTypeDecl extends ThingOfTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }
}

class PathGlobOfTypeDecl extends ThingOfTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
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

        return attrs + "entity " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class ErrTypeDecl extends ConstructableTypeDecl {
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

class APIRejectedTypeDecl extends ConstructableTypeDecl {
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

class APIFailedTypeDecl extends ConstructableTypeDecl {
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

class APIErrorTypeDecl extends ConstructableTypeDecl {
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

class APISuccessTypeDecl extends ConstructableTypeDecl {
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

class SomethingTypeDecl extends ConstructableTypeDecl {
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

class PairTypeDecl extends ConstructableTypeDecl {
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

class PrimitiveConceptTypeDecl extends InternalConceptTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "concept " + this.name + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
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
    readonly nestedEntityDecls: (OkTypeDecl | ErrTypeDecl)[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
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

class ExpandoableTypeDecl extends InternalConceptTypeDecl {
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

class StatusInfoFilter {
    xxxx;
    readonly standard: TypeSignature | undefined;
    readonly verbose: TypeSignature | undefined;

    constructor(standard: TypeSignature | undefined, verbose: TypeSignature | undefined) {
        this.standard = standard;
        this.verbose = verbose;
    }

    emit(): string {
        if(this.standard === undefined) {
            return "status []";
        }

        if(this.verbose === undefined) {
            return `status [${this.standard.tkeystr}]`;
        }

        return `status [${this.standard.tkeystr}, ${this.verbose.tkeystr}]`;
    }
}

class EnvironmentVariableInformation {
    readonly evname: string; //cstring
    readonly evtype: TypeSignature;
    readonly optdefault: ConstantExpressionValue | undefined;

    constructor(evname: string, evtype: TypeSignature, optdefault: ConstantExpressionValue | undefined) {
        this.evname = evname;
        this.evtype = evtype;
        this.optdefault = optdefault;
    }

    emit(fmt: CodeFormatter): string {
        if(this.optdefault === undefined) {
            return fmt.indent(`${this.evname}: ${this.evtype.tkeystr}`);
        }
        else {
            return fmt.indent(`${this.evname}: ${this.evtype.tkeystr} = ${this.optdefault.emit(true, fmt)}`);
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
    readonly pathglob: ConstantExpressionValue; //this is g\xxxx\* or g\xxxx\oftype or g\xxxx\_oftype, or constant, or an environment variable
    readonly accessInfo: ResourceAccessModes[];

    constructor(pathglob: ConstantExpressionValue, accessInfo: ResourceAccessModes[]) {
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

    readonly examples: InvokeExample[];

    readonly statusOutputs: StatusInfoFilter;
    readonly envVarRequirements: EnvironmentVariableInformation[];
    readonly resourceImpacts: ResourceInformation[] | "**" | "{}";

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: InvokeParameterDecl[], resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], examples: InvokeExample[], statusOutputs: StatusInfoFilter, envVarRequirements: EnvironmentVariableInformation[], resourceImpacts: ResourceInformation[] | "**" | "{}", body: BodyImplementation) {
        super(file, sinfo, attributes, name);
        
        this.params = params;
        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds

        this.examples = examples;

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

        let examples: string[] = [];
        if(this.examples.length !== 0) {
            examples = this.examples.map((ex) => ex.emit(fmt));
        }

        let status: string[] = [];
        const ss = this.statusOutputs.emit();
        if(ss !== undefined) {
            status = [ss];
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
        if(prec.length === 0 && postc.length === 0 && examples.length === 0 && status.length === 0 && evs.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc, ...examples, ...status, ...evs, ...resources].join("\n");
        }
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        const params = this.params.map((p) => p.emit(fmt)).join(", ");
        const result = this.resultType.tkeystr;

        const minfo = this.emitMetaInfo(fmt);
        return `${attrs}api ${this.name}(${params}): ${result} ${this.body.emit(fmt, minfo)}`;
    }
}

class TaskDecl extends AbstractNominalTypeDecl {
    readonly fields: MemberFieldDecl[] = [];
    readonly selfmethods: TaskMethodDecl[] = [];
    readonly actions: TaskActionDecl[] = [];

    xxxx;
    eventsInfo: TypeSignature[] | "{}" | "?" | undefined; //undefined means passthrough (or API is defined)
    statusInfo: StatusInfoFilter | "?" | undefined; //? means passthrough
    envVarRequirementInfo: EnvironmentVariableInformation[] | "?" | undefined; //? means passthrough
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
            if(this.eventsInfo === "{}") {
                mg.push(["event { }"]);
            }
            else if(this.eventsInfo === "?") {
                mg.push(["event { ? }"]);
            }
            else {
                mg.push([`event { ${this.eventsInfo.map((ei) => ei.tkeystr).join(", ")} }`]);
            }
        }
        if(this.statusInfo !== undefined) {
            if(this.statusInfo === "?") {
                mg.push(["status ?"]);
            }
            else {
                mg.push([this.statusInfo.emit()]);
            }
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
        if(this.envVarRequirementInfo !== undefined) {
            if(this.envVarRequirementInfo === "?") {
                mg.push(["env { ? }"]);
            }
            else {
                const vvl = this.envVarRequirementInfo.map((ev) => ev.emit(fmt));

                fmt.indentPush();
                const vvs = [vvl[0], ...vvl.slice(1).map((vv) => fmt.indent(vv))].join("\n");
                fmt.indentPop();

                mg.push([`env{ ${vvs} ${fmt.indent("}")}`]);
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
    readonly value: ConstantExpressionValue;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
        super(file, sinfo, attributes, name);

        this.declaredType = dtype;
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        const attr = this.attributes.length !== 0 ? this.attributes.map((a) => a.emit()).join(" ") + " " : "";
        return `${attr}const ${this.name}: ${this.declaredType.tkeystr} = ${this.value.emit(true, fmt)};`;
    }
}

class NamespaceUsing {
    readonly file: string;

    readonly fromns: FullyQualifiedNamespace;
    readonly asns: string | undefined;

    constructor(file: string, fromns: FullyQualifiedNamespace, asns: string | undefined) {
        this.file = file;

        this.fromns = fromns;
        this.asns = asns;
    }

    emit(): string {
        if(this.asns === undefined) {
            return `using ${this.fromns.emit()};`;
        }
        else {
            return `using ${this.fromns.emit()} as ${this.asns};`;
        }
    }
}

class NamespaceDeclaration {
    readonly istoplevel: boolean;
    readonly name: string; 
    readonly fullnamespace: FullyQualifiedNamespace;

    usings: NamespaceUsing[] = [];
    declaredNames: Set<string> = new Set<string>();
    declaredTypeNames: {name: string, hasterms: boolean}[] = []; //types, typedecls, and tasks
    declaredSubNSNames: Set<string> = new Set<string>();
    declaredMemberNames: Set<string> = new Set<string>(); //functions, apis, and consts

    subns: NamespaceDeclaration[] = [];

    consts: NamespaceConstDecl[] = [];
    functions: NamespaceFunctionDecl[] = [];
    typedecls: AbstractNominalTypeDecl[] = [];

    apis: APIDecl[] = [];
    tasks: TaskDecl[] = [];

    constructor(istoplevel: boolean, name: string, fullnamespace: FullyQualifiedNamespace) {
        this.istoplevel = istoplevel;
        this.name = name;
        this.fullnamespace = fullnamespace;
    }

    checkDeclNameClashNS(rname: string): boolean {
        if(!this.declaredNames.has(rname)) {
            return false;
        }

        //namespace always clashes with other namespaces and with simple member names
        if(this.declaredSubNSNames.has(rname) || this.declaredMemberNames.has(rname)) {
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
        if(this.declaredMemberNames.has(rname)) {
            return true;
        }

        //they also clash with each other even if they differ in termplates
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

        if(this.istoplevel) {
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

        if(!this.istoplevel) {
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
            this.toplevelNamespaces.push(new NamespaceDeclaration(true, ns, new FullyQualifiedNamespace([ns])));
        }

        return this.getToplevelNamespace(ns) as NamespaceDeclaration;
    }
}

export {
    WELL_KNOWN_RETURN_VAR_NAME, WELL_KNOWN_EVENTS_VAR_NAME, WELL_KNOWN_SRC_VAR_NAME,
    TemplateTermDeclExtraTag, TemplateTermDecl, TypeTemplateTermDecl, InvokeTemplateTermDecl, InvokeTemplateTypeRestrictionClause, InvokeTemplateTypeRestrictionClauseUnify, InvokeTemplateTypeRestrictionClauseSubtype, InvokeTemplateTypeRestriction, 
    AbstractDecl, 
    ConditionDecl, PreConditionDecl, PostConditionDecl, InvariantDecl, ValidateDecl,
    InvokeExampleKind, InvokeExample, InvokeExampleDeclInline, InvokeExampleDeclFile, 
    DeclarationAttibute, AbstractCoreDecl,
    InvokeParameterDecl, AbstractInvokeDecl, 
    LambdaDecl,
    ExplicitInvokeDecl,
    FunctionInvokeDecl, NamespaceFunctionDecl, TypeFunctionDecl,
    MethodDecl, TaskMethodDecl, TaskActionDecl,
    ConstMemberDecl, MemberFieldDecl,
    AbstractNominalTypeDecl, AdditionalTypeDeclTag,
    EnumTypeDecl,
    TypedeclTypeDecl,
    AbstractEntityTypeDecl, InternalEntityTypeDecl, PrimitiveEntityTypeDecl,
    RegexValidatorTypeDecl, CRegexValidatorTypeDecl, PathValidatorTypeDecl,
    ThingOfTypeDecl, StringOfTypeDecl, CStringOfTypeDecl, PathOfTypeDecl, PathFragmentOfTypeDecl, PathGlobOfTypeDecl,
    ConstructableTypeDecl, OkTypeDecl, ErrTypeDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APISuccessTypeDecl, SomethingTypeDecl, PairTypeDecl, MapEntryTypeDecl,
    AbstractCollectionTypeDecl, ListTypeDecl, StackTypeDecl, QueueTypeDecl, SetTypeDecl, MapTypeDecl,
    EventListTypeDecl,
    EntityTypeDecl, 
    AbstractConceptTypeDecl, InternalConceptTypeDecl, PrimitiveConceptTypeDecl, 
    OptionTypeDecl, ResultTypeDecl, APIResultTypeDecl, ExpandoableTypeDecl,
    ConceptTypeDecl, 
    DatatypeMemberEntityTypeDecl, DatatypeTypeDecl,
    StatusInfoFilter, EnvironmentVariableInformation, ResourceAccessModes, ResourceInformation, APIDecl,
    TaskDecl,
    NamespaceConstDecl, NamespaceUsing, NamespaceDeclaration,
    Assembly
};
