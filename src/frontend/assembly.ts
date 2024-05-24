
import { FullyQualifiedNamespace, TypeSignature, FunctionParameter, LambdaTypeSignature, RecursiveAnnotation, TemplateTypeSignature, VoidTypeSignature } from "./type";
import { Expression, BodyImplementation, ConstantExpressionValue } from "./body";

import { BuildLevel, CodeFormatter, SourceInfo } from "./build_decls";

class TypeTemplateTermDecl {
    readonly name: string;
    readonly tconstraint: TypeSignature;

    constructor(name: string, tconstraint: TypeSignature) {
        this.name = name;
        this.tconstraint = tconstraint;
    }

    emit(): string {
        if(this.tconstraint.emit(true) === "Any") {
            return this.name;
        }
        else {
            return `${this.name}: ${this.tconstraint.emit(true)}`;
        }
    }
}

class InvokeTemplateTermDecl {
    readonly name: string;
    readonly tconstraint: TypeSignature;
    readonly isinferable: boolean;

    constructor(name: string, tconstraint: TypeSignature, isinferable: boolean) {
        this.name = name;
        this.tconstraint = tconstraint;
        this.isinferable = isinferable;
    }

    emit(): string {
        if(this.tconstraint.emit(true) === "Any") {
            return `${this.name}${this.isinferable ? "?" : ""}`;
        }
        else {
            return `${this.name}${this.isinferable ? "?" : ""}: ${this.tconstraint.emit(true)}`;
        }
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
        return `type(${this.vname}) -> ${this.unifyinto.emit(true)}`;
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
        return `${this.t}@${this.subtype.emit(true)}`;
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

abstract class InvokeExample extends AbstractDecl {
    readonly istest: boolean;

    constructor(file: string, sinfo: SourceInfo, istest: boolean) {
        super(file, sinfo);
        this.istest = istest;
    }
}

class InvokeExampleDeclInline extends InvokeExample {
    readonly entries: {args: Expression[], output: Expression}[];

    constructor(file: string, sinfo: SourceInfo, istest: boolean, entries: {args: Expression[], output: Expression}[]) {
        super(file, sinfo, istest);
        this.entries = entries;
    }

    emit(fmt: CodeFormatter): string {
        const estr = this.entries.map((e) => `(${e.args.map((a) => a.emit(true, fmt)).join(", ")}) => ${e.output.emit(true, fmt)}`).join("; ");

        if(this.istest) {
            return fmt.indent(`test { ${estr} }`);
        }
        else {
            return fmt.indent(`example { ${estr} }`);
        }
    }
}

class InvokeExampleDeclFile extends InvokeExample {
    readonly filepath: string; //may use the ROOT and SRC environment variables

    constructor(file: string, sinfo: SourceInfo, istest: boolean, filepath: string) {
        super(file, sinfo, istest);
        this.filepath = filepath;
    }

    emit(fmt: CodeFormatter): string {
        if(this.istest) {
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
            return `${this.name}${this.tags.length === 0 ? "" : " [" + this.tags.map((t) => `${t.enumType.emit(true)}::${t.tag}`).join(", ") + "]"}`;
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

abstract class AbstractInvokeDecl extends AbstractCoreDecl {
    readonly recursive: RecursiveAnnotation;

    readonly params: FunctionParameter[];
    readonly resultType: TypeSignature;

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation) {
        super(file, sinfo, attributes, name);

        this.recursive = recursive;

        this.params = params;
        this.resultType = resultType;

        this.body = body;
    }

    emitSig(): [string, string] {
        const attrs = this.emitAttributes();

        let rec = "";
        if (this.recursive !== "no") {
            rec = this.recursive === "yes" ? "recursive " : "recursive? ";
        }

        let params = this.params.map((p) => p.emit()).join(", ");
        let result = (this.resultType instanceof VoidTypeSignature) ? "" : (": " + this.resultType.emit(true));

        return [`${attrs}${rec}`, `(${params})${result}`];
    }
}

class LambdaDecl extends AbstractInvokeDecl {
    readonly captureVarSet: Set<string>;

    readonly isAuto: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: "fn" | "pred", recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation, captureVarSet: Set<string>, isAuto: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body);

        this.captureVarSet = captureVarSet;
        this.isAuto = isAuto;
    }

    generateSig(sinfo: SourceInfo): TypeSignature {
        return new LambdaTypeSignature(sinfo, this.recursive, this.name as ("fn" | "pred"), this.params, this.resultType);
    }
    
    private emitCaptureInfo(): string {
        let capturev = "";
        if(this.captureVarSet.size !== 0) {
            capturev = "[" + Array.from(this.captureVarSet).sort().join(", ") + "]";
        }

        return "%*" + capturev + "*%";
    }

    emit(fmt: CodeFormatter): string {
        const ssig = this.emitSig();

        return `${ssig[0]}${this.name}${ssig[1]} ${this.body.emit(fmt, this.emitCaptureInfo())}`;
    }
}

abstract class ExplicitInvokeDecl extends AbstractInvokeDecl {
    readonly terms: InvokeTemplateTermDecl[];
    readonly termRestriction: InvokeTemplateTypeRestriction | undefined;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly examples: InvokeExample[];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[]) {
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
        const ssig = this.emitSig();
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
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[]) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }
}

class NamespaceFunctionDecl extends FunctionInvokeDecl {
    readonly fkind: "function" | "predicate" | "errtest" | "chktest";

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[], fkind: "function" | "predicate" | "errtest" | "chktest") {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);

        this.fkind = fkind;
    }

    getDeclarationTag(): string {
        return this.fkind;
    }
}

class TypeFunctionDecl extends FunctionInvokeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[]) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }

    getDeclarationTag(): string {
        return "function";
    }
}

class MethodDecl extends ExplicitInvokeDecl {
    readonly isThisRef: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[], isThisRef: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);

        this.isThisRef = isThisRef;
    }

    getDeclarationTag(): string {
        return (this.isThisRef ? "ref " : "") + "method";
    }
}

class TaskMethodDecl extends ExplicitInvokeDecl {
    readonly isSelfRef: boolean;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[], isSelfRef: boolean) {
        super(file, sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);

        this.isSelfRef = isSelfRef;
    }

    getDeclarationTag(): string {
        return (this.isSelfRef ? "ref " : "") + "method";
    }
}

class TaskActionDecl extends ExplicitInvokeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: FunctionParameter[], resultType: TypeSignature, body: BodyImplementation, terms: InvokeTemplateTermDecl[], termRestriction: InvokeTemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: InvokeExample[]) {
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
        return fmt.indent(`${this.emitAttributes()}const ${this.name}: ${this.declaredType.emit(true)} = ${this.value.emit(true, fmt)};`);
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
            return fmt.indent(`${attrs}field ${this.name}: ${this.declaredType.emit(true)};`);
        }
        else {
            return fmt.indent(`${attrs}field ${this.name}: ${this.declaredType.emit(true)} = ${this.defaultValue.emit(true, fmt)};`);
        }
    }
}

abstract class AbstractNominalTypeDecl extends AbstractDecl {
    readonly attributes: DeclarationAttibute[];
    readonly name: string;

    readonly terms: TypeTemplateTermDecl[] = [];
    readonly provides: TypeSignature[] = [];

    readonly invariants: InvariantDecl[] = [];
    readonly validates: ValidateDecl[] = [];

    readonly consts: ConstMemberDecl[] = [];
    readonly functions: TypeFunctionDecl[] = [];
    readonly methods: MethodDecl[] = [];

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

    emitTerms(): string {
        return this.terms.length !== 0 ? ("<" + this.terms.map((tt) => tt.emit()).join(", ") + ">") : "";
    }

    emitProvides(): string {
        return this.provides.length !== 0 ? (" provides" + this.provides.map((p) => p.emit(true)).join(", ")) : "";
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

class EnumTypeDecl extends AbstractNominalTypeDecl {
    readonly members: string[];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, members: string[]) {
        super(file, sinfo, attributes, name);

        this.members = members;
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const endl = this.members.map((e) => fmt.indent(e + ",")).join("\n");
        fmt.indentPop();

        return fmt.indent(`${attrs}enum ${this.name} {${endl}${fmt.indent("\n}")}`);
    }
}

class TypedeclTypeDecl extends AbstractNominalTypeDecl {
    readonly valuetype: TypeSignature;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, valuetype: TypeSignature) {
        super(file, sinfo, attributes, name);

        this.valuetype = valuetype;
    }

    emit(fmt: CodeFormatter): string {
        const tdcl = `${this.emitAttributes()}typedecl ${this.name}${this.emitTerms()} = ${this.valuetype.emit(true)}`;

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        if(bg.length === 0) {
            return tdcl + ";";
        }
        else {
            return tdcl + " &" + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
        }
    }
}

abstract class InternalEntityTypeDecl extends AbstractNominalTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
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

class ASCIIRegexValidatorTypeDecl extends InternalEntityTypeDecl {
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

class ThingOfTypeDecl extends InternalEntityTypeDecl {
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

class ASCIIStringOfTypeDecl extends ThingOfTypeDecl {
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

class EntityTypeDecl extends AbstractNominalTypeDecl {
    readonly fields: MemberFieldDecl[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.fields.length !== 0) {
            bg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

abstract class InternalConceptTypeDecl extends AbstractNominalTypeDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
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

class ConceptTypeDecl extends AbstractNominalTypeDecl {
    readonly fields: MemberFieldDecl[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.fields.length !== 0) {
            bg.push(this.fields.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        return attrs + "concept " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class DatatypeTypeDecl extends AbstractNominalTypeDecl {
    readonly members: MemberFieldDecl[] = [];

    xxxx;
    readonly associatedEntityDecls: EntityTypeDecl[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const mg: string[][] = [];
        if(this.members.length !== 0) {
            mg.push(this.members.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        const rootdecl = attrs + "datatype " + this.name + this.emitTerms() + this.emitProvides(); 
        let usingdecl = " of\n";
        if(mg.length !== 0) {
            usingdecl = " using {\n" + this.joinBodyGroups(mg) + fmt.indent("\n}\nof\n");
        }

        const edecls = this.associatedEntityDecls.map((aed) => {
            aed.emit(fmt)
        }).join("\n| ");

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        let etail = ";";
        if(bg.length !== 0) {
            etail = "& {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
        }

        return `${rootdecl}${usingdecl}${edecls}\n${etail}`;
    }
}

class StatusInfoFilter {
    readonly standard: TypeSignature | undefined;
    readonly verbose: TypeSignature | undefined;

    constructor(standard: TypeSignature | undefined, verbose: TypeSignature | undefined) {
        this.standard = standard;
        this.verbose = verbose;
    }

    emit(): string | undefined {
        if(this.standard === undefined) {
            return undefined;
        }

        if(this.verbose === undefined) {
            return `status ${this.standard.emit(true)}`;
        }

        return `status [${this.standard.emit(true)}, ${this.verbose.emit(true)}]`;
    }
}

class EnvironmentVariableInformation {
    readonly evname: string;
    readonly evtype: TypeSignature;
    readonly optdefault: Expression | undefined;

    constructor(evname: string, evtype: TypeSignature, optdefault: Expression | undefined) {
        this.evname = evname;
        this.evtype = evtype;
        this.optdefault = optdefault;
    }

    emit(fmt: CodeFormatter): string {
        if(this.optdefault === undefined) {
            return fmt.indent(`${this.evname}: ${this.evtype.emit(true)}`);
        }
        else {
            return fmt.indent(`${this.evname}: ${this.evtype.emit(true)} = ${this.optdefault.emit(true, fmt)}`);
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

enum ResourceAccessModes {
    get,     //no side effects and idempotent -- reads the value or list (elements) 
    modify,  //replaces or updates an existing value -- parent list modifications are implicit from the create/delete resource access info
    create,  //creates a new value or list (that did not previously exist)
    delete  //removes a value or list that may have previously existed
}

class ResourceInformation {
    readonly pathglob: ConstantExpressionValue; //this is g\xxxx\* or g\xxxx\oftype or g\xxxx\_oftype
    readonly accessInfo: ResourceAccessModes[];

    constructor(pathglob: ConstantExpressionValue, accessInfo: ResourceAccessModes[]) {
        this.pathglob = pathglob;
        this.accessInfo = accessInfo;
    }
}

class APIDecl extends AbstractCoreDecl {
    readonly params: FunctionParameter[];    
    readonly resultType: TypeSignature;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly examples: InvokeExample[];

    readonly statusOutputs: StatusInfoFilter;
    readonly envVarRequirements: EnvironmentVariableInformation[];
    readonly resourceImpacts: ResourceInformation[] | "*"; //* means any possible resource impact

    readonly body: BodyImplementation;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: FunctionParameter[], resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], examples: InvokeExample[], statusOutputs: StatusInfoFilter, envVarRequirements: EnvironmentVariableInformation[], resourceImpacts: ResourceInformation[] | "*", body: BodyImplementation) {
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

        let evs: string[] = [];
        if(this.envVarRequirements.length !== 0) {
            const vvl = this.envVarRequirements.map((ev) => ev.emit(fmt));

            fmt.indentPush();
            const vvs = [vvl[0], ...vvl.slice(1).map((vv) => fmt.indent(vv))].join("\n");
            fmt.indentPop();

            evs.push(`env{ ${vvs} ${fmt.indent("}")}`);
        }

        fmt.indentPop();

        if(prec.length === 0 && postc.length === 0 && examples.length === 0 && status.length === 0 && evs.length === 0) {
            return undefined;
        }
        else {
            return [...prec, ...postc, ...examples, ...status, ...evs].join("\n");
        }
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        const params = this.params.map((p) => p.emit()).join(", ");
        const result = this.resultType.emit(true);

        const minfo = this.emitMetaInfo(fmt);
        return `${attrs}api ${this.name}(${params}): ${result} ${this.body.emit(fmt, minfo)}`;
    }
}

abstract class TaskDecl extends AbstractNominalTypeDecl {
    readonly members: MemberFieldDecl[] = [];
    readonly actions: TaskActionDecl[] = [];

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    abstract getImplementsAPI(): APIDecl | undefined;

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const mg: string[][] = [];
        if(this.members.length !== 0) {
            mg.push(this.members.map((ff) => ff.emit(fmt)));
        }
        if(this.actions.length !== 0) {
            mg.push(this.actions.map((act) => act.emit(fmt)));
        }
        fmt.indentPop();

        let rootdecl = attrs + "task " + this.name + this.emitTerms(); 
        if(this.getImplementsAPI() !== undefined) {
            rootdecl += `implements ${this.getImplementsAPI()!.name}`;
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

class TaskDeclOnAPI extends TaskDecl {
    readonly api: APIDecl | undefined = undefined;
    
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    getImplementsAPI(): APIDecl | undefined {
        return this.api;
    }
}

class TaskDeclStandalone extends TaskDecl {
    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(file, sinfo, attributes, name);
    }

    getImplementsAPI(): APIDecl | undefined {
        return undefined;
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
        return `${attr}const ${this.name}: ${this.declaredType.emit(true)} = ${this.value.emit(true, fmt)};`;
    }
}

class NamespaceTypedef extends AbstractCoreDecl {
    terms: TypeTemplateTermDecl[] = [];
    boundType: TypeSignature;

    constructor(file: string, sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TypeTemplateTermDecl[], btype: TypeSignature) {
        super(file, sinfo, attributes, name);

        this.terms = terms;
        this.boundType = btype;
    }

    emit(): string {
        const attr = this.attributes.length !== 0 ? this.attributes.map((a) => a.emit()).join(" ") + " " : "";
        const tstr = this.terms.length !== 0 ? `<${this.terms.map((t) => t.emit()).join(", ")}> ` : "";
        return `${attr}type ${this.name}${tstr} = ${this.boundType.emit(true)};`;
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

    typeDefs: NamespaceTypedef[] = [];
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

        this.typeDefs.forEach((td) => {
            res += fmt.indent(td.emit() + "\n");
        });
        if(this.typeDefs.length !== 0) {
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

    getToplevelNamespace(ns: string): NamespaceDeclaration {
        return this.toplevelNamespaces.find((nsd) => nsd.name === ns) as NamespaceDeclaration;
    }

    ensureToplevelNamespace(ns: string): NamespaceDeclaration {
        if (!this.hasToplevelNamespace(ns)) {
            this.toplevelNamespaces.push(new NamespaceDeclaration(true, ns, new FullyQualifiedNamespace([ns])));
        }

        return this.getToplevelNamespace(ns);
    }
}

export {
    TypeTemplateTermDecl, InvokeTemplateTermDecl, InvokeTemplateTypeRestrictionClause, InvokeTemplateTypeRestrictionClauseUnify, InvokeTemplateTypeRestrictionClauseSubtype, InvokeTemplateTypeRestriction, 
    AbstractDecl, 
    ConditionDecl, PreConditionDecl, PostConditionDecl, InvariantDecl, ValidateDecl,
    InvokeExample, InvokeExampleDeclInline, InvokeExampleDeclFile, 
    DeclarationAttibute, AbstractCoreDecl,
    AbstractInvokeDecl, 
    LambdaDecl,
    ExplicitInvokeDecl,
    FunctionInvokeDecl, NamespaceFunctionDecl, TypeFunctionDecl,
    MethodDecl, TaskMethodDecl, TaskActionDecl,
    ConstMemberDecl, MemberFieldDecl,
    AbstractNominalTypeDecl, 
    EnumTypeDecl,
    TypedeclTypeDecl,
    InternalEntityTypeDecl, PrimitiveEntityTypeDecl,
    RegexValidatorTypeDecl, ASCIIRegexValidatorTypeDecl, PathValidatorTypeDecl,
    ThingOfTypeDecl, StringOfTypeDecl, ASCIIStringOfTypeDecl, PathOfTypeDecl, PathFragmentOfTypeDecl, PathGlobOfTypeDecl,
    ConstructableTypeDecl, OkTypeDecl, ErrTypeDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APISuccessTypeDecl, SomethingTypeDecl, MapEntryTypeDecl,
    AbstractCollectionTypeDecl, ListTypeDecl, StackTypeDecl, QueueTypeDecl, SetTypeDecl, MapTypeDecl,
    EntityTypeDecl, 
    InternalConceptTypeDecl, PrimitiveConceptTypeDecl, OptionTypeDecl, ResultTypeDecl, APIResultTypeDecl, ExpandoableTypeDecl,
    ConceptTypeDecl, 
    DatatypeTypeDecl,
    StatusInfoFilter, EnvironmentVariableInformation, ResourceAccessModes, ResourceInformation, APIDecl,
    TaskDecl, TaskDeclOnAPI, TaskDeclStandalone,
    NamespaceConstDecl, NamespaceTypedef, NamespaceUsing, NamespaceDeclaration,
    Assembly
};
