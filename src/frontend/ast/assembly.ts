//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { NominalTypeSignature, TypeSignature, FunctionTypeSignature, FunctionParameter } from "./type";
import { Expression, BodyImplementation, ConstantExpressionValue, LiteralExpressionValue } from "./body";

import { BuildLevel, SourceInfo } from "../build_decls";
import { BSQRegex } from "../bsqregex";
import { BSQPathValidator } from "../path_validator";

class TemplateTermDecl {
    readonly name: string;
    readonly isunique: boolean;
    readonly isgrounded: boolean;
    readonly isnumeric: boolean;
    readonly tconstraint: TypeSignature;

    constructor(name: string, isunique: boolean, isgrounded: boolean, isnumeric: boolean, tconstraint: TypeSignature) {
        this.name = name;
        this.isunique = isunique;
        this.isgrounded = isgrounded;
        this.isnumeric = isnumeric;
        this.tconstraint = tconstraint;
    }
}

class TemplateTypeRestriction {
    readonly t: TypeSignature;
    readonly isunique: boolean;
    readonly isgrounded: boolean;
    readonly tconstraint: TypeSignature;

    constructor(t: TypeSignature, isunique: boolean, isgrounded: boolean, tconstraint: TypeSignature) {
        this.t = t;
        this.isunique = isunique;
        this.isgrounded = isgrounded;
        this.tconstraint = tconstraint;
    }
}

class TypeConditionRestriction {
    readonly constraints: TemplateTypeRestriction[];

    constructor(constraints: TemplateTypeRestriction[]) {
        this.constraints = constraints;
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
}

class InvokeSampleDeclInline {
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
}

class InvokeSampleDeclFile {
    readonly sinfo: SourceInfo;
    readonly istest: boolean;
    readonly filepath: string; //may use the $root and $src meta variables

    constructor(sinfo: SourceInfo, istest: boolean, filepath: string) {
        this.sinfo = sinfo;
        this.istest = istest;
        this.filepath = filepath;
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
}

class ValidateDecl {
    readonly sinfo: SourceInfo;
    readonly exp: ConstantExpressionValue;

    constructor(sinfo: SourceInfo, exp: ConstantExpressionValue) {
        this.sinfo = sinfo;
        this.exp = exp;
    }
}

class InvokeDecl {
    readonly namespace: string;
    readonly startSourceLocation: SourceInfo;
    readonly endSourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly recursive: "yes" | "no" | "cond";

    readonly terms: TemplateTermDecl[];
    readonly termRestrictions: TypeConditionRestriction | undefined;

    readonly isThisRef: boolean;
    readonly params: FunctionParameter[];
    
    readonly resultType: TypeSignature;

    readonly preconditions: PreConditionDecl[];
    readonly postconditions: PostConditionDecl[];

    readonly samples: (InvokeSampleDeclInline | InvokeSampleDeclFile)[];

    readonly isPCodeFn: boolean;
    readonly isPCodePred: boolean;
    readonly captureVarSet: Set<string>;
    readonly captureTemplateSet: Set<string>;

    readonly body: BodyImplementation | undefined;

    constructor(ns: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], isThisRef: boolean, resultType: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], samples: (InvokeSampleDeclInline | InvokeSampleDeclFile)[], isPCodeFn: boolean, isPCodePred: boolean, captureVarSet: Set<string>, captureTemplateSet: Set<string>, body: BodyImplementation | undefined) {
        this.namespace = ns;
        this.startSourceLocation = sinfoStart;
        this.endSourceLocation = sinfoEnd;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.recursive = recursive;

        this.terms = terms;
        this.termRestrictions = termRestrictions;

        this.isThisRef = isThisRef;
        this.params = params;

        this.resultType = resultType;

        this.preconditions = preconds;
        this.postconditions = postconds;
        this.samples = samples;

        this.isPCodeFn = isPCodeFn;
        this.isPCodePred = isPCodePred;
        this.captureVarSet = captureVarSet;
        this.captureTemplateSet = captureTemplateSet;
        this.body = body;
    }

    generateSig(sinfo: SourceInfo): TypeSignature {
        return new FunctionTypeSignature(sinfo, this.isThisRef, this.recursive, this.params, this.resultType, this.isPCodePred);
    }

    static createPCodeInvokeDecl(namespce: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", params: FunctionParameter[], resultInfo: TypeSignature, captureVarSet: Set<string>, captureTemplateSet: Set<string>, body: BodyImplementation, isPCodeFn: boolean, isPCodePred: boolean) {
        return new InvokeDecl(namespce, sinfoStart, sinfoEnd, srcFile, attributes, recursive, [], undefined, params, false, resultInfo, [], [], [], isPCodeFn, isPCodePred, captureVarSet, captureTemplateSet, body);
    }

    static createStandardInvokeDecl(namespace: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], isThisRef: boolean, resultInfo: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], samples: (InvokeSampleDeclInline | InvokeSampleDeclFile)[], body: BodyImplementation | undefined) {
        return new InvokeDecl(namespace, sinfoStart, sinfoEnd, srcFile, attributes, recursive, terms, termRestrictions, params, isThisRef, resultInfo, preconds, postconds, samples, false, false, new Set<string>(), new Set<string>(), body);
    }

    static createSynthesisInvokeDecl(namespace: string, sinfoStart: SourceInfo, sinfoEnd: SourceInfo, srcFile: string, attributes: string[], recursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], termRestrictions: TypeConditionRestriction | undefined, params: FunctionParameter[], isThisRef: boolean, resultInfo: TypeSignature, preconds: PreConditionDecl[], postconds: PostConditionDecl[], samples: (InvokeSampleDeclInline | InvokeSampleDeclFile)[], body: BodyImplementation) {
        return new InvokeDecl(namespace, sinfoStart, sinfoEnd, srcFile, attributes, recursive, terms, termRestrictions, params, isThisRef, resultInfo, preconds, postconds, samples, false, false, new Set<string>(), new Set<string>(), body);
    }
}

interface OOMemberDecl {
    getName(): string;
    hasAttribute(attr: string): boolean;
}

class StaticMemberDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }

    getName(): string {
        return this.name;
    }

    hasAttribute(attr: string): boolean {
        return this.attributes.includes(attr);
    }
}

class StaticFunctionDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }

    hasAttribute(attr: string): boolean {
        return this.attributes.includes(attr);
    }
}

class MemberFieldDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly declaredType: TypeSignature;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], name: string, dtype: TypeSignature) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
    }

    getName(): string {
        return this.name;
    }

    hasAttribute(attr: string): boolean {
        return this.attributes.includes(attr);
    }
}

class MemberMethodDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.invoke = invoke;
    }

    getName(): string {
        return this.name;
    }

    hasAttribute(attr: string): boolean {
        return this.attributes.includes(attr);
    }
}

class ControlFieldDecl implements OOMemberDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly defaultValue: ConstantExpressionValue | undefined;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], name: string, dtype: TypeSignature, defaultValue: ConstantExpressionValue | undefined) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
        this.defaultValue = defaultValue;
    }

    getName(): string {
        return this.name;
    }

    hasAttribute(attr: string): boolean {
        return this.attributes.includes(attr);
    }
}

class OOPTypeDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly terms: TemplateTermDecl[];

    readonly provides: [TypeSignature, TypeConditionRestriction | undefined][];

    readonly invariants: InvariantDecl[];
    readonly validates: ValidateDecl[];

    readonly staticMembers: StaticMemberDecl[];
    readonly staticFunctions: StaticFunctionDecl[];
    readonly memberFields: MemberFieldDecl[];
    readonly memberMethods: MemberMethodDecl[];

    readonly nestedEntityDecls: Map<string, EntityTypeDecl>;

    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
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

class ConceptTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        super(sourceLocation, srcFile, attributes, ns, name, terms, provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, nestedEntityDecls);
    }
}

class EntityTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[], provides: [TypeSignature, TypeConditionRestriction | undefined][],
        invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        nestedEntityDecls: Map<string, EntityTypeDecl>) {
        super(sourceLocation, srcFile, attributes, ns, name, terms, provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, nestedEntityDecls);
    }
}

class TaskStatusEffect {
    readonly statusinfo: TypeSignature[];

    constructor(statusinfo: TypeSignature[]) {
        this.statusinfo = statusinfo;
    }
}

class TaskEventEffect {
    readonly eventinfo: TypeSignature[];

    constructor(eventinfo: TypeSignature[]) {
        this.eventinfo = eventinfo;
    }
}

class TaskEnvironmentEffect {
    readonly evars: {vv: string, isw: boolean}[]; //string "*" is wildcard

    constructor(evars: {vv: string, isw: boolean}[]) {
        this.evars = evars;
    }
}

class TaskResourceEffect {
    readonly pathdescriptor: TypeSignature; //the resource validator
    readonly pathglob: ConstantExpressionValue | undefined; //returns a glob string of type PathGlob<pathdescriptor>
    readonly isread: boolean;
    readonly iswrite: boolean;

    constructor(pathdescriptor: TypeSignature, pathglob: ConstantExpressionValue | undefined, isread: boolean, iswrite: boolean) {
        this.pathdescriptor = pathdescriptor;
        this.pathglob = pathglob;
        this.isread = isread;
        this.iswrite = iswrite;
    }
}

class TaskTypeDecl extends OOPTypeDecl {
    readonly econtrol: ControlFieldDecl[];
    readonly actions: MemberMethodDecl[];
    readonly mainfunc: StaticFunctionDecl;
    readonly onfuncs: { onCanel: MemberMethodDecl | undefined, onFailure: MemberMethodDecl | undefined, onTimeout: MemberMethodDecl | undefined };
    readonly lfuncs: { logStart: StaticFunctionDecl | undefined, logEnd: StaticFunctionDecl | undefined, taskEnsures: MemberMethodDecl | undefined, taskWarns: MemberMethodDecl | undefined };

    readonly statuseffect: TaskStatusEffect;
    readonly eventeffect: TaskEventEffect
    readonly enveffect: TaskEnvironmentEffect;
    readonly resourceeffect: TaskResourceEffect[];

    constructor(sourceLocation: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, terms: TemplateTermDecl[],
        validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[],
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[],
        econtrol: ControlFieldDecl[],
        mainfunc: StaticFunctionDecl,
        actions: MemberMethodDecl[],
        onfuncs: { onCanel: MemberMethodDecl | undefined, onFailure: MemberMethodDecl | undefined, onTimeout: MemberMethodDecl | undefined },
        lfuncs: { logStart: StaticFunctionDecl | undefined, logEnd: StaticFunctionDecl | undefined, taskEnsures: MemberMethodDecl | undefined, taskWarns: MemberMethodDecl | undefined },
        statuseffect: TaskStatusEffect, eventeffect: TaskEventEffect, enveffect: TaskEnvironmentEffect, resourceeffect: TaskResourceEffect[]) {
        super(sourceLocation, srcFile, attributes, ns, name, terms, [[new NominalTypeSignature(sourceLocation, "Core", ["Task"], undefined), undefined]], [], validates, staticMembers, staticFunctions, memberFields, memberMethods, new Map<string, EntityTypeDecl>());

        this.econtrol = econtrol;
        this.mainfunc = mainfunc;
        this.actions = actions;
        this.onfuncs = onfuncs;
        this.lfuncs = lfuncs;

        this.statuseffect = statuseffect;
        this.eventeffect = eventeffect;
        this.enveffect = enveffect;
        this.resourceeffect = resourceeffect;
    }
}

class NamespaceConstDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly declaredType: TypeSignature;
    readonly value: ConstantExpressionValue;

    constructor(srcInfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, dtype: TypeSignature, value: ConstantExpressionValue) {
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

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;

    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.invoke = invoke;
    }
}

class NamespaceOperatorDecl {
    readonly sourceLocation: SourceInfo;
    readonly srcFile: string;

    readonly attributes: string[];
    readonly ns: string;
    readonly name: string;
    readonly invoke: InvokeDecl;

    constructor(sinfo: SourceInfo, srcFile: string, attributes: string[], ns: string, name: string, invoke: InvokeDecl) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;

        this.attributes = attributes;
        this.ns = ns;
        this.name = name;

        this.invoke = invoke;
    }
}

class NamespaceTypedef {
    readonly attributes: string[];

    readonly ns: string;
    readonly name: string;
    readonly boundType: TypeSignature;

    constructor(attributes: string[], ns: string, name: string, btype: TypeSignature) {
        this.attributes = attributes;

        this.ns = ns;
        this.name = name;
        this.boundType = btype;
    }
}

class NamespaceUsing {
    readonly fromns: string;
    readonly asns: string;
    readonly names: string[];

    constructor(fromns: string, asns: string, names: string[]) {
        this.fromns = fromns;
        this.asns = asns;
        this.names = names;
    }
}

class NamespaceDeclaration {
    readonly ns: string;

    usings: NamespaceUsing[];
    declaredNames: Set<string>;

    typeDefs: Map<string, NamespaceTypedef>;
    consts: Map<string, NamespaceConstDecl>;
    functions: Map<string, NamespaceFunctionDecl>;
    operators: Map<string, NamespaceOperatorDecl[]>;
    concepts: Map<string, ConceptTypeDecl>;
    objects: Map<string, EntityTypeDecl>;
    
    tasks: Map<string, TaskTypeDecl>;
    msgformats: Map<string, InfoTemplate>;
    stringformats: Map<string, StringTemplate>;

    constructor(ns: string) {
        this.ns = ns;
        this.usings = [];
        this.declaredNames = new Set<string>();

        this.typeDefs = new Map<string, NamespaceTypedef>();
        this.consts = new Map<string, NamespaceConstDecl>();
        this.functions = new Map<string, NamespaceFunctionDecl>();
        this.operators = new Map<string, NamespaceOperatorDecl[]>();
        this.concepts = new Map<string, ConceptTypeDecl>();
        this.objects = new Map<string, EntityTypeDecl>();

        this.tasks = new Map<string, TaskTypeDecl>();
        this.msgformats = new Map<string, InfoTemplate>();
        this.stringformats = new Map<string, StringTemplate>();
    }

    checkDeclNameClash(rname: string): boolean {
        return this.typeDefs.has(rname) || this.consts.has(rname) || this.functions.has(rname) || this.concepts.has(rname) || this.objects.has(rname) || 
        this.tasks.has(rname) || this.msgformats.has(rname) || this.stringformats.has(rname);
    }
}

class InfoTemplate {
}

class InfoTemplateRecord extends InfoTemplate {
    readonly entries: { name: string, value: InfoTemplate }[];

    constructor(entries: { name: string, value: InfoTemplate }[]) {
        super();
        this.entries = entries;
    }
}

class InfoTemplateTuple extends InfoTemplate {
    readonly entries: InfoTemplate[];

    constructor(entries: InfoTemplate[]) {
        super();
        this.entries = entries;
    }
}

class InfoTemplateConst extends InfoTemplate {
    readonly lexp: LiteralExpressionValue;

    constructor(lexp: LiteralExpressionValue) {
        super();
        this.lexp = lexp;
    }
}

class InfoTemplateMacro extends InfoTemplate {
    readonly macro: string;

    constructor(macro: string) {
        super();
        this.macro = macro;
    }
}

class InfoTemplateValue extends InfoTemplate {
    readonly argpos: number;
    readonly argtype: TypeSignature;

    constructor(argpos: number, argtype: TypeSignature) {
        super();
        this.argpos = argpos;
        this.argtype = argtype;
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
    TemplateTermDecl, TemplateTypeRestriction, TypeConditionRestriction, PreConditionDecl, PostConditionDecl, InvokeSampleDeclInline, InvokeSampleDeclFile, InvokeDecl,
    OOMemberDecl, InvariantDecl, ValidateDecl, StaticMemberDecl, StaticFunctionDecl, MemberFieldDecl, MemberMethodDecl, ControlFieldDecl, OOPTypeDecl, ConceptTypeDecl, EntityTypeDecl, 
    TaskStatusEffect, TaskEventEffect, TaskEnvironmentEffect, TaskResourceEffect, TaskTypeDecl,
    InfoTemplate, InfoTemplateRecord, InfoTemplateTuple, InfoTemplateConst, InfoTemplateMacro, InfoTemplateValue,
    StringTemplate,
    NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, NamespaceTypedef, NamespaceUsing, NamespaceDeclaration,
    Assembly
};
