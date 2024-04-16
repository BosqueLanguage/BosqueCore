//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeSignature, FunctionTypeSignature, FunctionParameter } from "./type";
import { Expression, BodyImplementation, ConstantExpressionValue } from "./body";

import { BuildLevel, CodeFormatter, FullyQualifiedNamespace, SourceInfo } from "../build_decls";

enum TemplateTermSpecialRestrictions {
    grounded,
    unique
};

class TemplateTermDecl {
    readonly name: string;
    readonly specialconstraints: TemplateTermSpecialRestrictions[];
    readonly tconstraint: TypeSignature;

    constructor(name: string, specialconstraints: TemplateTermSpecialRestrictions[], tconstraint: TypeSignature) {
        this.name = name;
        this.specialconstraints = specialconstraints;
        this.tconstraint = tconstraint;
    }

    isGrounded(): boolean { return this.specialconstraints.includes(TemplateTermSpecialRestrictions.grounded); }
    isUnique(): boolean { return this.specialconstraints.includes(TemplateTermSpecialRestrictions.unique); }

    emit(): string {
        const scstr = this.specialconstraints.length === 0 ? "" : ` ${this.specialconstraints.map((sc) => sc.toString()).join(" ")}`;
        return `${this.name}${scstr} ${this.tconstraint.emit()}`;
    }
}

class TemplateTypeRestriction {
    readonly t: TypeSignature;
    readonly specialconstraints: TemplateTermSpecialRestrictions[];
    readonly tconstraint: TypeSignature;

    constructor(t: TypeSignature, specialconstraints: TemplateTermSpecialRestrictions[], tconstraint: TypeSignature) {
        this.t = t;
        this.specialconstraints = specialconstraints;
        this.tconstraint = tconstraint;
    }

    isGrounded(): boolean { return this.specialconstraints.includes(TemplateTermSpecialRestrictions.grounded); }
    isUnique(): boolean { return this.specialconstraints.includes(TemplateTermSpecialRestrictions.unique); }

    emit(): string {
        const scstr = this.specialconstraints.length === 0 ? "" : ` ${this.specialconstraints.map((sc) => sc.toString()).join(" ")}`;
        return `${this.t.emit()}${scstr} ${this.tconstraint.emit()}`;
    }
}

class TypeConditionRestriction {
    readonly constraints: TemplateTypeRestriction[];

    constructor(constraints: TemplateTypeRestriction[]) {
        this.constraints = constraints;
    }

    emit(withparens: boolean): string {
        if(this.constraints.length === 0) {
            return "";
        }
        else {
            const cc = "when " + this.constraints.map((ctr) => ctr.emit()).join(" && ");
            return withparens ? `{${cc}}` : cc;
        }
    }
}

class PreConditionDecl {
    readonly sinfo: SourceInfo;
    readonly level: BuildLevel;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, level: BuildLevel, exp: Expression) {
        this.sinfo = sinfo;
        this.level = level;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("requires" + (this.level !== "release" ? (" " + this.level) : "") + this.exp.emit() + ";");
    }
}

class PostConditionDecl {
    readonly sinfo: SourceInfo;
    readonly level: BuildLevel;
    readonly exp: Expression;

    constructor(sinfo: SourceInfo, level: BuildLevel, exp: Expression) {
        this.sinfo = sinfo;
        this.level = level;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("ensures" + (this.level !== "release" ? (" " + this.level) : "") + this.exp.emit() + ";");
    }
}

class InvokeExampleDeclInline {
    readonly sinfo: SourceInfo;
    readonly istest: boolean;
    readonly args: string; //a tuple of the arguments
    readonly output: string;

    constructor(sinfo: SourceInfo, istest: boolean, args: string, output: string) {
        this.sinfo = sinfo;
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

class InvokeExampleDeclFile {
    readonly sinfo: SourceInfo;
    readonly istest: boolean;
    readonly filepath: string; //may use the ROOT and SRC environment variables

    constructor(sinfo: SourceInfo, istest: boolean, filepath: string) {
        this.sinfo = sinfo;
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

class InvariantDecl {
    readonly sinfo: SourceInfo;
    readonly level: BuildLevel;
    readonly exp: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, level: BuildLevel, exp: ConstantExpressionValue) {
        this.sinfo = sinfo;
        this.level = level;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("invariant" + (this.level !== "release" ? (" " + this.level) : "") + this.exp.emit() + ";");
    }
}

class ValidateDecl {
    readonly sinfo: SourceInfo;
    readonly exp: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, exp: ConstantExpressionValue) {
        this.sinfo = sinfo;
        this.exp = exp;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent("validate" + this.exp.emit() + ";");
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

abstract class AbstractDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: DeclarationAttibute[];
    readonly name: string;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], name: string) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
    }

    hasAttribute(aname: string): boolean {
        return this.attributes.find((attr) => attr.name === aname) !== undefined;
    }

    emitAttributes(): string {
        return this.attributes.map((attr) => attr.emit()).join(" ");
    }
}
abstract class AbstractInvokeDecl extends AbstractDecl {
    readonly ns: FullyQualifiedNamespace;
    readonly startSourceLocation: SourceInfo;
    readonly endSourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: DeclarationAttibute[];
    readonly recursive: "yes" | "no" | "cond";

    readonly terms: TemplateTermDecl[];
    readonly termRestrictions: TypeConditionRestriction | undefined;

    readonly receiverTag: InvokeReceiverTag;
    readonly params: FunctionParameter[];
    
    readonly resultType: TypeSignature;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[];

    readonly isPCodeFn: boolean;
    readonly isPCodePred: boolean;
    readonly captureVarSet: Set<string>;
    readonly captureTemplateSet: Set<string>;

    readonly body: BodyImplementation;

    constructor(ns: FullyQualifiedNamespace, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], receiverTag: InvokeReceiverTag, resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[], isPCodeFn: boolean, isPCodePred: boolean, captureVarSet: Set<string>, captureTemplateSet: Set<string>, body: BodyImplementation) {
        this.ns = ns;
        this.startSourceLocation = sinfoStart;
        this.endSourceLocation = sinfoEnd;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.recursive = recursive;

        this.terms = terms;
        this.termRestrictions = termRestrictions;

        this.receiverTag = receiverTag;
        this.params = params;

        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;
        this.examples = examples;

        this.isPCodeFn = isPCodeFn;
        this.isPCodePred = isPCodePred;
        this.captureVarSet = captureVarSet;
        this.captureTemplateSet = captureTemplateSet;
        this.body = body;
    }

    generateSig(sinfo: SourceInfo): TypeSignature {
        return new FunctionTypeSignature(sinfo, this.receiverTag, this.recursive, this.params, this.resultType, this.isPCodePred);
    }

    static createPCodeInvokeDecl(namespce: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultInfo: TypeSignature, captureVarSet: Set<string>, captureTemplateSet: Set<string>, body: BodyImplementation, isPCodeFn: boolean, isPCodePred: boolean) {
        return new InvokeDecl(namespce, sinfoStart, sinfoEnd, srcFile, attributes, recursive, [], undefined, params, InvokeReceiverTag.Std, resultInfo, [], [], [], isPCodeFn, isPCodePred, captureVarSet, captureTemplateSet, body);
    }

    static createStandardInvokeDecl(namespace: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], receiverTag: InvokeReceiverTag, resultInfo: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], samples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[], body: BodyImplementation) {
        return new InvokeDecl(namespace, sinfoStart, sinfoEnd, srcFile, attributes, recursive, terms, termRestrictions, params, receiverTag, resultInfo, preconds, postconds, samples, false, false, new Set<string>(), new Set<string>(), body);
    }

    static createSynthesisInvokeDecl(namespace: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], receiverTag: InvokeReceiverTag, resultInfo: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], samples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[], body: BodyImplementation) {
        return new InvokeDecl(namespace, sinfoStart, sinfoEnd, srcFile, attributes, recursive, terms, termRestrictions, params, receiverTag, resultInfo, preconds, postconds, samples, false, false, new Set<string>(), new Set<string>(), body);
    }

    private emitSig(fmt: CodeFormatter | undefined, name: string | undefined): string {
        let attrs = "";
        if(this.attributes.length !== 0) {
            attrs = this.attributes.map((attr) => attr.emit()).join(" ") + " ";
        }

        let rec = "";
        if(this.recursive !== "no") {
            rec = this.recursive + " ";
        }

        let params = this.params.map((p) => p.name + ": " + p.type.emit()).join(", ");

        if(name === undefined) {
            const ff = this.isPCodePred ? "pred" : "fn";

            return `${rec}${ff}(${params}): ${this.resultType.emit()}`;
        }
        else {
            let terms = "";
            if(this.terms.length !== 0) {
                terms = "<" + this.terms.map((tt) => tt.emit()).join(", ") + ">";
            }

            let restricts = "";
            if(this.termRestrictions !== undefined) {
                restricts = this.termRestrictions.emit(true) + " ";
            }

            let ttinfo: string;
            if(this.receiverTag === InvokeReceiverTag.Std) {
                ttinfo = "function";
            }
            else if(this.receiverTag === InvokeReceiverTag.This || this.receiverTag === InvokeReceiverTag.Self) {
                ttinfo = "method";
            }
            else if(this.receiverTag === InvokeReceiverTag.ThisRef || this.receiverTag === InvokeReceiverTag.SelfRef) {
                ttinfo = "method ref";
            }
            else {
                ttinfo = "action";
            }

            return (fmt as CodeFormatter).indent(`${attrs}${rec}${ttinfo} ${restricts}${name}${terms}(${params}): ${this.resultType.emit()}`);
        }
    }

    private emitMetaInfo(fmt: CodeFormatter): string {
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

    emitPCode(): string {
        return this.emitSig(undefined, undefined) + this.body.emit(undefined, this.emitCaptureInfo());
    }

    emitStdInvokeDecl(fmt: CodeFormatter, name: string) {
        const sig = this.emitSig(fmt, name);

        fmt.indentPush();
        const meta = this.emitMetaInfo(fmt);
        fmt.indentPop();

        const body = this.body.emit(fmt, this.emitCaptureInfo());

        if(meta === "") {
            return fmt.indent(sig + body);
        }
        else {
            return fmt.indent(sig + "\n" + meta + "\n" + fmt.indent(body));
        }
    }
}

abstract class AbstractLambdaDecl extends AbstractInvokeDecl {
    xxxx;
}

class ParametricLambdaDecl extends AbstractLambdaDecl {
    xxxx;
}

class StdLambdaDecl extends AbstractLambdaDecl {
    xxxx;
}

abstract class ExplicitInvokeDecl extends AbstractInvokeDecl {
    xxxx;
}

abstract class ParametricExplicitInvokeDecl extends ExplicitInvokeDecl {
    xxxx;
}

abstract class StdExplicitInvokeDecl extends ExplicitInvokeDecl {
    xxxx;
}

abstract class ParametricFunctionInvokeDecl extends ParametricExplicitInvokeDecl {
    xxxx;
}

abstract class StdFunctionInvokeDecl extends StdExplicitInvokeDecl {
    xxxx;
}

class NamespaceParametricFunctionDecl extends ParametricFunctionInvokeDecl {
    xxxx;
}

class NamespaceStdFunctionDecl extends StdExplicitInvokeDecl {
    xxxx;
}

abstract class ParametricMethodInvokeDecl extends ParametricExplicitInvokeDecl {
    xxxx;
}

class ParametricMethodDecl extends ParametricMethodInvokeDecl {
    xxxx;
}

class ParametricRefMethodDecl extends ParametricMethodInvokeDecl {
    xxxx;
}

class ParametricTaskMethodDecl extends ParametricMethodInvokeDecl {
    xxxx;
}

class ParametricTaskRefMethodDecl extends ParametricMethodInvokeDecl {
    xxxx;
}

class ParametricTaskActionDecl extends ParametricMethodInvokeDecl {
    xxxx;
}

abstract class StdMethodInvokeDecl extends StdExplicitInvokeDecl {
    xxxx;
}

class StdMethodDecl extends StdMethodInvokeDecl {
    xxxx;
}

class StdRefMethodDecl extends StdMethodInvokeDecl {
    xxxx;
}

class StdTaskMethodDecl extends StdMethodInvokeDecl {
    xxxx;
}

class StdTaskRefMethodDecl extends StdMethodInvokeDecl {
    xxxx;
}

class StdTaskActionDecl extends StdMethodInvokeDecl {
    xxxx;
}


class StaticMemberDecl extends OOMemberDecl {
    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
        super(srcInfo, srcFile, attributes, name);

        this.declaredType = dtype;
        this.value = value;
    }

    emit(fmt: CodeFormatter): string {
        let attrs = "";
        if(this.attributes.length !== 0) {
            attrs = this.attributes.map((attr) => attr.emit()).join(" ") + " ";
        }
        return fmt.indent(`${attrs}const ${this.name}: ${this.declaredType.emit()} = ${this.value.emit()};`);
    }
}

class StaticFunctionDecl extends OOMemberDecl {
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], name: string, invoke: InvokeDecl) {
        super(sinfo, srcFile, attributes, name);
        
        this.invoke = invoke;
    }

    emit(fmt: CodeFormatter): string {
        return this.invoke.emitStdInvokeDecl(fmt, this.name);
    }
}

class MemberFieldDecl extends OOMemberDecl {
    readonly declaredType: TypeSignature;
    readonly defaultValue: ConstantExpressionValue | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], name: string, dtype: TypeSignature, dvalue: ConstantExpressionValue | undefined) {
        super(srcInfo, srcFile, attributes, name);
        
        this.declaredType = dtype;
        this.defaultValue = dvalue;
    }

    emit(fmt: CodeFormatter): string {
        let attrs = "";
        if(this.attributes.length !== 0) {
            attrs = this.attributes.map((attr) => attr.emit()).join(" ") + " ";
        }

        if(this.defaultValue === undefined) {
            return fmt.indent(`${attrs}field ${this.name}: ${this.declaredType.emit()};`);
        }
        else {
            return fmt.indent(`${attrs}field ${this.name}: ${this.declaredType.emit()} = ${this.defaultValue.emit()};`);
        }
    }
}

class MemberMethodDecl extends OOMemberDecl {
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], name: string, invoke: InvokeDecl) {
        super(sinfo, srcFile, attributes, name);
        
        this.invoke = invoke;
    }

    emit(fmt: CodeFormatter): string {
        return this.invoke.emitStdInvokeDecl(fmt, this.name);
    }
}

abstract class TypeDecl {
    readonly sinfo: SourceInfo;
    readonly srcFile: string;

    readonly ns: FullyQualifiedNamespace;
    readonly name: string;

    constructor(sinfo: SourceInfo, srcFile: string, ns: FullyQualifiedNamespace, name: string) {
        this.sinfo = sinfo;
        this.srcFile = srcFile;
        this.ns = ns;
        this.name = name;
    }
}

abstract class OOPTypeDecl extends TypeDecl {
    readonly attributes: DeclarationAttibute[];

    readonly provides: [TypeSignature, TypeConditionRestriction | undefined][];

    readonly invariants: InvariantDecl[];
    readonly validates: ValidateDecl[];

    readonly staticMembers: StaticMemberDecl[];
    readonly staticFunctions: StaticFunctionDecl[];
    readonly memberFields: MemberFieldDecl[];
    readonly memberMethods: MemberMethodDecl[];

    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        this.sourceLocation = sourceLocation;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.invariants = invariants;
        this.validates = validates;
        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
        this.nestedEntityDecls = nestedEntityDecls;
    }
}

class StdOOTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        this.sourceLocation = sourceLocation;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.invariants = invariants;
        this.validates = validates;
        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
        this.nestedEntityDecls = nestedEntityDecls;
    }
}

class ParametricOOTypeDecl extends OOPTypeDecl {
    readonly terms: TemplateTermDecl[];
    readonly nestedEntityDecls: Map<string, EntityTypeDecl>;

    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        this.sourceLocation = sourceLocation;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.invariants = invariants;
        this.validates = validates;
        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
        this.nestedEntityDecls = nestedEntityDecls;
    }
}

class BuiltinDecl extends TypeDecl {
}

class EnumDecl extends TypeDecl {
    readonly members: string[];

    constructor(sinfo: SourceInfo, srcFile: string, ns: FullyQualifiedNamespace, name: string, members: string[]) {
        super(sinfo, srcFile, ns, name);
        this.members = members;
    }

    emit(fmt: CodeFormatter): string {
        return fmt.indent(`enum ${this.name} {${this.members.join(",\n")}}`);
    }
}

class TypedeclDecl extends TypeDecl {
    xxxx;
}































class ConceptTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        super(sourceLocation, srcFile, attributes, ns, name, terms, provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, nestedEntityDecls);
    }
}

class EntityTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        super(sourceLocation, srcFile, attributes, ns, name, terms, provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, nestedEntityDecls);
    }
}

class StdEntityTypeDecl extends EntityTypeDecl {
}

class StatusInfo {
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

class APIDecl {
    readonly startSourceLocation: SourceInfo;
    readonly endSourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: DeclarationAttibute[];
    readonly ns: FullyQualifiedNamespace;
    readonly name: string;

    readonly params: FunctionParameter[];    
    readonly resultType: TypeSignature;

    readonly preconds: PreConditionDecl[];
    readonly postconds: PostConditionDecl[];

    readonly examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[];

    readonly statusOutputs: StatusInfo;
    readonly envVarRequirements: EnvironmentVariableInformation[];
    readonly resourceImpacts: ResourceInformation[];

    readonly body: BodyImplementation | undefined;

    constructor(sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, params: FunctionParameter[], resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], examples: (InvokeExampleDeclInline | InvokeExampleDeclFile)[], statusOutputs: StatusInfo, envVarRequirements: EnvironmentVariableInformation[], resourceImpacts: ResourceInformation[], body: BodyImplementation | undefined) {
        this.startSourceLocation = sinfoStart;
        this.endSourceLocation = sinfoEnd;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        
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
}


class MemberActionDecl extends OOMemberDecl {
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], name: string, invoke: InvokeDecl) {
        super(sinfo, srcFile, attributes, name);

        this.invoke = invoke;
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
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: DeclarationAttibute[];
    readonly ns: FullyQualifiedNamespace;
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.declaredType = dtype;
        this.value = value;
    }
}

class NamespaceFunctionDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: DeclarationAttibute[];
    readonly ns: FullyQualifiedNamespace;
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.invoke = invoke;
    }
}

class NamespaceTypedef {
    readonly attributes: DeclarationAttibute[];

    readonly ns: FullyQualifiedNamespace;
    readonly name: string;
    readonly boundType: TypeSignature;

    constructor(attributes: DeclarationAttibute[], ns: FullyQualifiedNamespace, name: string, btype: TypeSignature) {
        this.attributes = attributes;

        this.ns = ns;
        this.name = name;
        this.boundType = btype;
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

class StringTemplate {
    readonly str: string;

    //
    //TODO: want to pre-process this for formats and such
    //

    constructor(str: string) {
        this.str = str;
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
    TemplateTermSpecialRestrictions, TemplateTermDecl, TemplateTypeRestriction, TypeConditionRestriction, PreConditionDecl, PostConditionDecl, InvokeExampleDeclInline, InvokeExampleDeclFile, 
    DeclarationAttibute, InvokeReceiverTag, InvokeDecl,
    OOMemberDecl, InvariantDecl, ValidateDecl, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, OOPTypeDecl, ConceptTypeDecl, EntityTypeDecl, 
    StatusInfo, EnvironmentVariableInformation, ResourceAccessModes, ResourceInformation, APIDecl,
    MemberActionDecl, TaskDecl, TaskDeclOnAPI, TaskDeclStandalone,
    StringTemplate,
    NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, NamespaceTypedef, NamespaceUsing, NamespaceDeclaration,
    Assembly
};
