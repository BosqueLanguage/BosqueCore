
import { TypeSignature, FunctionParameter, LambdaTypeSignature, RecursiveAnnotation } from "./type";
import { Expression, BodyImplementation, ConstantExpressionValue } from "./body";

import { BuildLevel, CodeFormatter, FullyQualifiedNamespace, SourceInfo } from "../build_decls";

class TemplateTermDecl {
    readonly name: string;
    readonly isGrounded: boolean;
    readonly isUnique: boolean;
    readonly tconstraint: TypeSignature;

    constructor(name: string, isGrounded: boolean, isUnique: boolean, tconstraint: TypeSignature) {
        this.name = name;
        this.isGrounded = isGrounded;
        this.isUnique = isUnique;
        this.tconstraint = tconstraint;
    }

    emit(): string {
        let scstr = "";
        if(this.isGrounded) {
            scstr = " grounded";
        }
        if(this.isUnique) {
            scstr = " unique";
        }

        return `${this.name}${scstr} ${this.tconstraint.emit()}`;
    }
}

class TemplateTypeRestriction {
    readonly t: TypeSignature;
    readonly isGrounded: boolean;
    readonly isUnique: boolean;
    readonly tconstraint: TypeSignature;

    constructor(t: TypeSignature, isGrounded: boolean, isUnique: boolean, tconstraint: TypeSignature) {
        this.t = t;
        this.isGrounded = isGrounded;
        this.isUnique = isUnique;
        this.tconstraint = tconstraint;
    }

    emit(): string {
        let scstr = "";
        if(this.isGrounded) {
            scstr = " grounded";
        }
        if(this.isUnique) {
            scstr = " unique";
        }

        return `when ${this.t.emit()} ${scstr} ${this.tconstraint.emit()}`;
    }
}

abstract class AbstractDecl {
    readonly sinfo: SourceInfo;

    constructor(sinfo: SourceInfo) {
        this.sinfo = sinfo;
    }

    abstract emit(fmt: CodeFormatter): string;
}

abstract class ConditionDecl extends AbstractDecl {
    readonly diagnosticTag: string | undefined;

    constructor(srcInfo: SourceInfo, diagnosticTag: string | undefined) {
        super(srcInfo);
        this.diagnosticTag = diagnosticTag;
    }

    emitDiagnosticTag(): string {
        return this.diagnosticTag === undefined ? "" : `[${this.diagnosticTag}]`;
    }
}

class PreConditionDecl extends ConditionDecl {
    readonly level: BuildLevel;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, tag: string | undefined, level: BuildLevel, exp: Expression) {
        super(sinfo, tag);

        this.level = level;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("requires" + this.emitDiagnosticTag() + (this.level !== "release" ? (" " + this.level) : "") + this.exp.emit(true) + ";");
    }
}

class PostConditionDecl extends ConditionDecl {
    readonly level: BuildLevel;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, tag: string | undefined, level: BuildLevel, exp: Expression) {
        super(sinfo, tag);

        this.level = level;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("ensures" + this.emitDiagnosticTag() + (this.level !== "release" ? (" " + this.level) : "") + this.exp.emit(true) + ";");
    }
}

class InvariantDecl extends ConditionDecl {
    readonly level: BuildLevel;
    readonly exp: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, tag: string | undefined, level: BuildLevel, exp: ConstantExpressionValue) {
        super(sinfo, tag);

        this.level = level;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("invariant" + this.emitDiagnosticTag() + (this.level !== "release" ? (" " + this.level) : "") + this.exp.emit(true) + ";");
    }
}

class ValidateDecl extends ConditionDecl {
    readonly exp: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, tag: string | undefined, exp: ConstantExpressionValue) {
        super(sinfo, tag);

        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("validate" + this.emitDiagnosticTag() + this.exp.emit(true) + ";");
    }
}

class InvokeExampleDeclInline extends AbstractDecl {
    readonly istest: boolean;
    readonly args: string; //a tuple of the arguments
    readonly output: string;

    constructor(sinfo: SourceInfo, istest: boolean, args: string, output: string) {
        super(sinfo);

        this.istest = istest;
        this.args = args;
        this.output = output;
    }

    emit(fmt: CodeFormatter): string {
        if(this.istest) {
            return fmt.indent(`test ${this.args} -> ${this.output};`);
        }
        else {
            return fmt.indent(`example ${this.args} -> ${this.output};`);
        }
    }
}

class InvokeExampleDeclFile extends AbstractDecl {
    readonly istest: boolean;
    readonly filepath: string; //may use the ROOT and SRC environment variables

    constructor(sinfo: SourceInfo, istest: boolean, filepath: string) {
        super(sinfo);

        this.istest = istest;
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
    readonly tags: {enumType: string, tag: string}[]; //tags are enum names

    constructor(name: string, tags: {enumType: string, tag: string}[]) {
        this.name = name;
        this.tags = tags;
    }

    emit(): string {
        return `${this.name}${this.tags.length === 0 ? "" : " [" + this.tags.map((t) => `${t.enumType}.${t.tag}`).join(", ") + "]"}`;
    }
}

abstract class AbstractCoreDecl extends AbstractDecl {
    readonly attributes: DeclarationAttibute[];
    readonly name: string;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string) {
        super(sinfo);
        
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
    readonly resultType: TypeSignature | undefined;

    readonly body: BodyImplementation;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation) {
        super(sinfo, attributes, name);

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
        let result = this.resultType === undefined ? "" : (": " + this.resultType.emit());

        return [`${attrs}${rec}`, `(${params})${result}`];
    }
}

class LambdaDecl extends AbstractInvokeDecl {
    readonly captureVarSet: Set<string>;
    readonly captureTemplateSet: Set<string>;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: "fn" | "pred", recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation, captureVarSet: Set<string>, captureTemplateSet: Set<string>) {
        super(sinfo, attributes, name, recursive, params, resultType, body);

        this.captureVarSet = captureVarSet;
        this.captureTemplateSet = captureTemplateSet;
    }

    generateSig(sinfo: SourceInfo): TypeSignature {
        return new LambdaTypeSignature(sinfo, this.recursive, this.name as ("fn" | "pred"), this.params, this.resultType);
    }
    
    private emitCaptureInfo(): string {
        
        let capturet = "";
        if(this.captureTemplateSet.size !== 0) {
            capturet = "<" + Array.from(this.captureTemplateSet).sort().join(", ") + ">";
        }

        let capturev = "";
        if(this.captureVarSet.size !== 0) {
            capturev = "[" + Array.from(this.captureVarSet).sort().join(", ") + "]";
        }

        return "%*" + [capturet, capturev].join(" ") + "*%";
    }

    emit(fmt: CodeFormatter): string {
        const ssig = this.emitSig();

        return `${ssig[0]}${this.name}${ssig[1]} ${this.body.emit(fmt, this.emitCaptureInfo())}`;
    }
}

abstract class ExplicitInvokeDecl extends AbstractInvokeDecl {
    readonly terms: TemplateTermDecl[];
    readonly termRestriction: TemplateTypeRestriction | undefined;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[];

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation, terms: TemplateTermDecl[], termRestriction: TemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[]) {
        super(sinfo, attributes, name, recursive, params, resultType, body);

        this.terms = terms;
        this.termRestriction = termRestriction;

        this.preconditions = preconditions;
        this.postconditions = postconditions;
        this.examples = examples;
    }

    emitMetaInfo(fmt: CodeFormatter): string {
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

        return [...prec, ...postc, ...examples].join("\n");
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
            restricts = "{" + this.termRestriction.emit() + "} ";
        }

        const ttinfo = this.getDeclarationTag();

        return (fmt as CodeFormatter).indent(`${ssig[0]} ${ttinfo} ${restricts}${this.name}${terms}${ssig[1]} ${this.body.emit(fmt, meta)}`);
    }

    abstract getDeclarationTag(): string;
}

abstract class FunctionInvokeDecl extends ExplicitInvokeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation, terms: TemplateTermDecl[], termRestriction: TemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[]) {
        super(sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }

    getDeclarationTag(): string {
        return "function";
    }
}

class NamespaceFunctionDecl extends FunctionInvokeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation, terms: TemplateTermDecl[], termRestriction: TemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[]) {
        super(sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }
}

class TypeFunctionDecl extends FunctionInvokeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation, terms: TemplateTermDecl[], termRestriction: TemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[]) {
        super(sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }
}

class MethodDecl extends ExplicitInvokeDecl {
    readonly isThisRef: boolean;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation, terms: TemplateTermDecl[], termRestriction: TemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[], isThisRef: boolean) {
        super(sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);

        this.isThisRef = isThisRef;
    }

    getDeclarationTag(): string {
        return (this.isThisRef ? "ref " : "") + "method";
    }
}

class TaskMethodDecl extends ExplicitInvokeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation, terms: TemplateTermDecl[], termRestriction: TemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[]) {
        super(sinfo, attributes, name, recursive, params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }

    getDeclarationTag(): string {
        return "method";
    }
}

class TaskActionDecl extends ExplicitInvokeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: FunctionParameter[], resultType: TypeSignature | undefined, body: BodyImplementation, terms: TemplateTermDecl[], termRestriction: TemplateTypeRestriction | undefined, preconditions: PreConditionDecl[], postconditions: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[]) {
        super(sinfo, attributes, name, "no", params, resultType, body, terms, termRestriction, preconditions, postconditions, examples);
    }

    getDeclarationTag(): string {
        return "action";
    }
}

class ConstMemberDecl extends AbstractCoreDecl {
    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
        super(sinfo, attributes, name);

        this.declaredType = dtype;
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}const ${this.name}: ${this.declaredType.emit()} = ${this.value.emit(true, fmt)};`);
    }
}

class MemberFieldDecl extends AbstractCoreDecl {
    readonly declaredType: TypeSignature;
    readonly defaultValue: ConstantExpressionValue | undefined;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, dvalue: ConstantExpressionValue | undefined) {
        super(sinfo, attributes, name);
        
        this.declaredType = dtype;
        this.defaultValue = dvalue;
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

abstract class TypeDecl extends AbstractDecl {
    constructor(sinfo: SourceInfo) {
        super(sinfo);
    }
}

abstract class AbstractNominalTypeDecl extends TypeDecl {
    readonly attributes: DeclarationAttibute[];
    readonly name: string;
    
    readonly terms: TemplateTermDecl[];
    readonly provides: TypeSignature[];

    readonly invariants: InvariantDecl[];
    readonly validates: ValidateDecl[];

    readonly consts: ConstMemberDecl[];
    readonly functions: TypeFunctionDecl[];
    readonly methods: MethodDecl[];

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo);

        this.attributes = attributes;
        this.name = name;

        this.terms = terms;
        this.provides = provides;

        this.invariants = invariants;
        this.validates = validates;

        this.consts = consts;
        this.functions = functions;
        this.methods = methods;
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
        return this.provides.length !== 0 ? (" provides" + this.provides.map((p) => p[0].emit() + (p[1] === undefined ? "" : p[1].emit(true))).join(", ")) : "";
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

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[], members: string[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);

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

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[], valuetype: TypeSignature) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);

        this.valuetype = valuetype;
    }

    emit(fmt: CodeFormatter): string {
        const tdcl = `${this.emitAttributes()}typedecl ${this.name}${this.emitTerms()} = ${this.valuetype.emit()}`;

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
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class PrimitiveEntityTypeDecl extends InternalEntityTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, provides: TypeSignature[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, [], provides, [], [], consts, functions, methods);
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

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, regex: string) {
        super(sinfo, attributes, name, [], [], [], [], [], [], []);

        this.regex = regex;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}validator ${this.name} = ${this.regex};`);
    }
}

class ASCIIRegexValidatorTypeDecl extends InternalEntityTypeDecl {
    readonly regex: string;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, regex: string) {
        super(sinfo, attributes, name, [], [], [], [], [], [], []);

        this.regex = regex;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}validator ${this.name} = ${this.regex};`);
    }
}

class PathValidatorTypeDecl extends InternalEntityTypeDecl {
    readonly pathglob: string;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, pathglob: string) {
        super(sinfo, attributes, name, [], [], [], [], [], [], []);

        this.pathglob = pathglob;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`${this.emitAttributes()}validator ${this.name} = ${this.pathglob};`);
    }
}

class ThingOfTypeDecl extends InternalEntityTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
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
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class ASCIIStringOfTypeDecl extends ThingOfTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class PathOfTypeDecl extends ThingOfTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class PathFragmentOfTypeDecl extends ThingOfTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class PathGlobOfTypeDecl extends ThingOfTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

abstract class ConstructableTypeDecl extends InternalEntityTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class OkTypeDecl extends ConstructableTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + "Result::" + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class ErrTypeDecl extends ConstructableTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + "Result::" + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class APIOkTypeDecl extends ConstructableTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + "Result::" + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class APIErrTypeDecl extends ConstructableTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + "Result::" + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class SomethingTypeDecl extends ConstructableTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class MapEntryEntityTypeDecl extends ConstructableTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
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
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
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
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class StackypeDecl extends AbstractCollectionTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class QueueTypeDecl extends AbstractCollectionTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class SetTypeDecl extends AbstractCollectionTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class MapTypeDecl extends AbstractCollectionTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);
    }
}

class EntityTypeDecl extends AbstractNominalTypeDecl {
    readonly members: MemberFieldDecl[];

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[], members: MemberFieldDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);

        this.members = members;
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.members.length !== 0) {
            bg.push(this.members.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        return attrs + "entity " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

abstract class InternalConceptTypeDecl extends AbstractNominalTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, [], [], consts, functions, methods);
    }
}

class PrimitiveConceptTypeDecl extends InternalConceptTypeDecl {
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, [], [], consts, functions, methods);
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
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[]) {
        super(sinfo, attributes, name, terms, provides, consts, functions, methods);
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
    readonly nestedEntityDecls: (OkTypeDecl | ErrTypeDecl)[];

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[], nestedEntityDecls: (OkTypeDecl | ErrTypeDecl)[]) {
        super(sinfo, attributes, name, terms, provides, consts, functions, methods);

        this.nestedEntityDecls = nestedEntityDecls;
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
    readonly nestedEntityDecls: (APIOkTypeDecl | APIErrTypeDecl)[];

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[], nestedEntityDecls: (APIOkTypeDecl | APIErrTypeDecl)[]) {
        super(sinfo, attributes, name, terms, provides, consts, functions, methods);

        this.nestedEntityDecls = nestedEntityDecls;
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
    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[]) {
        super(sinfo, attributes, name, terms, provides, [], [], []);
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
    readonly members: MemberFieldDecl[];

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[], members: MemberFieldDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);

        this.members = members;
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        fmt.indentPush();
        const bg = this.emitBodyGroups(fmt);
        if(this.members.length !== 0) {
            bg.push(this.members.map((ff) => ff.emit(fmt)));
        }
        fmt.indentPop();

        return attrs + "concept " + this.name + this.emitTerms() + this.emitProvides() + " {\n" + this.joinBodyGroups(bg) + fmt.indent("\n}");
    }
}

class DatatypeTypeDecl extends AbstractNominalTypeDecl {
    readonly members: MemberFieldDecl[];

    readonly associatedEntityDecls: EntityTypeDecl[];

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, terms: TemplateTermDecl[], provides: TypeSignature[], invariants: InvariantDecl[], validates: ValidateDecl[], consts: ConstMemberDecl[], functions: TypeFunctionDecl[], methods: MethodDecl[], members: MemberFieldDecl[], associatedEntityDecls: EntityTypeDecl[]) {
        super(sinfo, attributes, name, terms, provides, invariants, validates, consts, functions, methods);

        this.members = members;
        this.associatedEntityDecls = associatedEntityDecls;
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
    readonly standard: TypeSignature[];
    readonly verbose: TypeSignature[];

    constructor(standard: TypeSignature[], verbose: TypeSignature[]) {
        this.standard = standard;
        this.verbose = verbose;
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

    readonly preconds: PreConditionDecl[];
    readonly postconds: PostConditionDecl[];

    readonly examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[];

    readonly statusOutputs: StatusInfoFilter;
    readonly envVarRequirements: EnvironmentVariableInformation[];
    readonly resourceImpacts: ResourceInformation[];

    readonly body: BodyImplementation;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, params: FunctionParameter[], resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[], statusOutputs: StatusInfoFilter, envVarRequirements: EnvironmentVariableInformation[], resourceImpacts: ResourceInformation[], body: BodyImplementation | undefined) {
        super(sinfo, attributes, name);
        
        this.params = params;
        this.resultType = resultType;

        this.preconds = preconds;
        this.postconds = postconds

        this.examples = examples;

        this.statusOutputs = statusOutputs;
        this.envVarRequirements = envVarRequirements;
        this.resourceImpacts = resourceImpacts;

        this.body = body;
    }

    emit(fmt: CodeFormatter): string {
        const attrs = this.emitAttributes();

        const params = this.params.map((p) => p.emit()).join(", ");
        const result = this.resultType.emit();

        const preconds = this.preconds.map((pc) => pc.emit(fmt)).join("\n");
        const postconds = this.postconds.map((pc) => pc.emit(fmt)).join("\n");

        const examples = this.examples.map((ex) => ex.emit(fmt)).join("\n");

        const statusOutputs = this.statusOutputs.emit(fmt);
        const envVarRequirements = this.envVarRequirements.map((ev) => ev.emit(fmt)).join("\n");
        const resourceImpacts = this.resourceImpacts.map((ri) => ri.emit(fmt)).join("\n");

        const body = this.body !== undefined ? this.body.emit(fmt) : "";

        return `${attrs}api ${this.name}(${params}): ${result} {\n${preconds}\n${postconds}\n${examples}\n${statusOutputs}\n${envVarRequirements}\n${resourceImpacts}\n${body}\n}`;
    }
}

class TaskDecl {
    readonly startSourceLocation: SourceInfo;
    readonly endSourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: DeclarationAttibute[];
    readonly ns: FullyQualifiedNamespace;
    readonly name: string;

    readonly staticMembers: StaticMemberDecl[];
    readonly staticFunctions: StaticFunctionDecl[];
    readonly memberFields: MemberFieldDecl[];
    readonly memberMethods: MemberMethodDecl[];

    readonly memberActions: MemberActionDecl[];

    readonly mainAction: string;
    readonly onCancelAction: string | undefined;
    readonly onTimeoutAction: string | undefined;
    readonly onErrorAction: string | undefined;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[], memberActions: MemberActionDecl[], mainAction: string, onCancelAction: string | undefined, onTimeoutAction: string | undefined, onErrorAction: string | undefined) {
        this.startSourceLocation = sinfo;
        this.endSourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;

        this.memberActions = memberActions;

        this.mainAction = mainAction;
        this.onCancelAction = onCancelAction;
        this.onTimeoutAction = onTimeoutAction;
        this.onErrorAction = onErrorAction;
    }
}

class TaskDeclOnAPI extends TaskDecl {
    readonly api: APIDecl;
    
    constructor(sinfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[], memberActions: MemberActionDecl[], onCancelAction: string | undefined, onTimeoutAction: string | undefined, onErrorAction: string | undefined, api: APIDecl) {
        super(sinfo, srcFile, attributes, ns, name, staticMembers, staticFunctions, memberFields, memberMethods, memberActions, api.name, onCancelAction, onTimeoutAction, onErrorAction);

        this.api = api;
    }
}

class TaskDeclStandalone extends TaskDecl {
    readonly params: FunctionParameter[];    
    readonly resultType: TypeSignature;

    readonly preconds: PreConditionDecl[];
    readonly postcondsWarn: PostConditionDecl[];
    readonly postcondsBlock: PostConditionDecl[];

    readonly examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[];

    readonly statusOutputs: StatusInfo;
    readonly envVarRequirements: EnvironmentVariableInformation[];
    readonly resourceImpacts: ResourceInformation[];

    constructor(sinfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[], memberActions: MemberActionDecl[], onCancelAction: string | undefined, onTimeoutAction: string | undefined, onErrorAction: string | undefined, params: FunctionParameter[], resultType: TypeSignature, preconds: PreConditionDecl[], postcondsWarn: PostConditionDecl[], postcondsBlock: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[], statusOutputs: StatusInfo, envVarRequirements: EnvironmentVariableInformation[], resourceImpacts: ResourceInformation[]) {
        super(sinfo, srcFile, attributes, ns, name, staticMembers, staticFunctions, memberFields, memberMethods, memberActions, "main", onCancelAction, onTimeoutAction, onErrorAction);

        this.params = params;
        this.resultType = resultType;

        this.preconds = preconds;
        this.postcondsWarn = postcondsWarn;
        this.postcondsBlock = postcondsBlock;

        this.examples = examples;

        this.statusOutputs = statusOutputs;
        this.envVarRequirements = envVarRequirements;
        this.resourceImpacts = resourceImpacts;
    }
}

class NamespaceConstDecl {
    readonly sinfo: SourceInfo;
    readonly attributes: DeclarationAttibute[];
    
    readonly name: string;
    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
        this.sinfo = sinfo;
        this.attributes = attributes;

        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        const attr = this.attributes.length !== 0 ? this.attributes.map((a) => a.emit()).join(" ") + " " : "";
        return `${attr}const ${this.name}: ${this.declaredType.emit()} = ${this.value.emit(true, fmt)};`;
    }
}

class NamespaceTypedef {
    readonly sinfo: SourceInfo;
    readonly attributes: DeclarationAttibute[];

    readonly name: string;
    readonly boundType: TypeSignature;

    constructor(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, btype: TypeSignature) {
        this.sinfo = sinfo;
        this.attributes = attributes;

        this.name = name;
        this.boundType = btype;
    }

    emit(): string {
        const attr = this.attributes.length !== 0 ? this.attributes.map((a) => a.emit()).join(" ") + " " : "";
        return `${attr}typedef ${this.name} = ${this.boundType.emit()};`;
    }
}

class NamespaceUsing {
    readonly fromns: FullyQualifiedNamespace;
    readonly asns: string;
    readonly names: string[];

    constructor(fromns: FullyQualifiedNamespace, asns: string, names: string[]) {
        this.fromns = fromns;
        this.asns = asns;
        this.names = names;
    }

    emit(): string {
        return `using ${this.fromns} as ${this.asns};`;
    }
}

class NamespaceDeclaration {
    readonly ns: FullyQualifiedNamespace;
    readonly name: string; 

    usings: NamespaceUsing[];
    declaredNames: Set<string>;

    subns: Map<string, NamespaceDeclaration>;

    typeDefs: Map<string, NamespaceTypedef>;
    consts: Map<string, NamespaceConstDecl>;
    functions: Map<string, NamespaceFunctionDecl>;
    operators: Map<string, NamespaceOperatorDecl[]>;
    concepts: Map<string, ConceptTypeDecl>;
    entities: Map<string, EntityTypeDecl>;

    apis: Map<string, APIDecl>;
    tasks: Map<string, TaskDecl>;
    stringformats: Map<string, StringTemplate>;

    constructor(ns: FullyQualifiedNamespace, name: string) {
        this.ns = ns;
        this.name = name;

        this.usings = [];
        this.declaredNames = new Set<string>();

        this.subns = new Map<string, NamespaceDeclaration>();

        this.typeDefs = new Map<string, NamespaceTypedef>();
        this.consts = new Map<string, NamespaceConstDecl>();
        this.functions = new Map<string, NamespaceFunctionDecl>();
        this.operators = new Map<string, NamespaceOperatorDecl[]>();
        this.concepts = new Map<string, ConceptTypeDecl>();
        this.entities = new Map<string, EntityTypeDecl>();

        this.apis = new Map<string, APIDecl>();
        this.stringformats = new Map<string, StringTemplate>();
    }

    checkDeclNameClash(rname: string, hastemplates: boolean): boolean {
        if(!this.declaredNames.has(rname)) {
            return false;
        }

        if(hastemplates) {
            return this.functions.has(rname) || this.concepts.has(rname) || this.entities.has(rname);
        }
        else {
            return this.typeDefs.has(rname) || this.consts.has(rname) || this.functions.has(rname) || this.concepts.has(rname) || this.entities.has(rname) || this.apis.has(rname) || this.stringformats.has(rname);
        }
    }
}

class Assembly {
    private m_namespaceMap: Map<string, NamespaceDeclaration> = new Map<string, NamespaceDeclaration>();
    private m_conceptMap: Map<string, ConceptTypeDecl> = new Map<string, ConceptTypeDecl>();
    private m_objectMap: Map<string, EntityTypeDecl> = new Map<string, EntityTypeDecl>();
    private m_taskMap: Map<string, TaskTypeDecl> = new Map<string, TaskTypeDecl>();

    m_literalRegexs: BSQRegex[] = [];
    m_literalPaths: BSQPathValidator[] = [];

    tryGetConceptTypeForFullyResolvedName(name: string): ConceptTypeDecl | undefined {
        return this.m_conceptMap.get(name);
    }

    tryGetObjectTypeForFullyResolvedName(name: string): EntityTypeDecl | undefined {
        return this.m_objectMap.get(name);
    }

    tryGetTaskTypeForFullyResolvedName(name: string): TaskTypeDecl | undefined {
        return this.m_taskMap.get(name);
    }

    tryGetValidatorForFullyResolvedName(name: string): BSQRegex | undefined {
        return this.m_literalRegexs.find((re) => re.regexid === name);
    }

    tryGetPathValidatorForFullyResolvedName(name: string): BSQPathValidator | undefined {
        return this.m_literalPaths.find((pre) => pre.pathid === name);
    }

    hasNamespace(ns: string): boolean {
        return this.m_namespaceMap.has(ns);
    }

    getNamespace(ns: string): NamespaceDeclaration {
        return this.m_namespaceMap.get(ns) as NamespaceDeclaration;
    }

    ensureNamespace(ns: string): NamespaceDeclaration {
        if (!this.hasNamespace(ns)) {
            this.m_namespaceMap.set(ns, new NamespaceDeclaration(ns));
        }

        return this.getNamespace(ns);
    }

    getNamespaces(): NamespaceDeclaration[] {
        let decls: NamespaceDeclaration[] = [];
        this.m_namespaceMap.forEach((v, k) => {
            decls.push(v);
        });
        return decls;
    }

    addConceptDecl(resolvedName: string, concept: ConceptTypeDecl) {
        this.m_conceptMap.set(resolvedName, concept);
    }

    addObjectDecl(resolvedName: string, object: EntityTypeDecl) {
        this.m_objectMap.set(resolvedName, object);
    }

    addTaskDecl(resolvedName: string, task: TaskTypeDecl) {
        this.m_taskMap.set(resolvedName, task);
    }

    addValidatorRegex(validator: BSQRegex) {
        let ere = this.m_literalRegexs.findIndex((lre) => BSQRegex.areRedundantLiterals(lre, validator));
        if(ere === -1) {
            ere = this.m_literalRegexs.length;
            this.m_literalRegexs.push(validator);
        }
    }

    addValidatorPath(validator: BSQPathValidator) {
        this.m_literalPaths.push(validator);
    }

    addLiteralRegex(re: BSQRegex) {
        const ere = this.m_literalRegexs.findIndex((lre) => BSQRegex.areRedundantLiterals(lre, re));
        if(ere === -1) {
            this.m_literalRegexs.push(re);
        }
    }

    getAllEntities(): EntityTypeDecl[] {
        return [...this.m_objectMap].map((mm) => mm[1]);
    }
}

export {
    TemplateTermDecl, TemplateTypeRestriction, 
    AbstractDecl, 
    ConditionDecl, PreConditionDecl, PostConditionDecl, InvariantDecl, ValidateDecl,
    InvokeExampleDeclInline, InvokeExampleDeclFile, 
    DeclarationAttibute, AbstractCoreDecl,
    AbstractInvokeDecl, 
    LambdaDecl,
    ExplicitInvokeDecl,
    FunctionInvokeDecl, NamespaceFunctionDecl, TypeFunctionDecl,
    MethodDecl, TaskMethodDecl, TaskActionDecl,
    ConstMemberDecl, MemberFieldDecl,
    TypeDecl, AbstractNominalTypeDecl, 
    EnumTypeDecl,
    TypedeclTypeDecl,
    InternalEntityTypeDecl, PrimitiveEntityTypeDecl,
    RegexValidatorTypeDecl, ASCIIRegexValidatorTypeDecl, PathValidatorTypeDecl,
    ThingOfTypeDecl, StringOfTypeDecl, ASCIIStringOfTypeDecl, PathOfTypeDecl, PathFragmentOfTypeDecl, PathGlobOfTypeDecl,
    ConstructableTypeDecl, OkTypeDecl, ErrTypeDecl, APIOkTypeDecl, APIErrTypeDecl, SomethingTypeDecl, MapEntryEntityTypeDecl,
    AbstractCollectionTypeDecl, ListTypeDecl, StackypeDecl, QueueTypeDecl, SetTypeDecl, MapTypeDecl,
    EntityTypeDecl, 
    InternalConceptTypeDecl, PrimitiveConceptTypeDecl, OptionTypeDecl, ResultTypeDecl, APIResultTypeDecl, ExpandoableTypeDecl,
    ConceptTypeDecl, 
    DatatypeTypeDecl,


    StatusInfoFilter, EnvironmentVariableInformation, ResourceAccessModes, ResourceInformation, APIDecl,
    MemberActionDecl, TaskDecl, TaskDeclOnAPI, TaskDeclStandalone,
    StringTemplate,
    NamespaceConstDecl, NamespaceOperatorDecl, NamespaceTypedef, NamespaceUsing, NamespaceDeclaration,
    Assembly
};
