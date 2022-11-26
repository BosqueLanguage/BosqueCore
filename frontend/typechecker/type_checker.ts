//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { Assembly, BuildLevel, ConceptTypeDecl, EntityTypeDecl, InvariantDecl, InvokeDecl, isBuildLevelEnabled, MemberFieldDecl, MemberMethodDecl, NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, NamespaceTypedef, OOMemberDecl, OOPTypeDecl, PathValidator, PreConditionDecl, StaticFunctionDecl, StaticMemberDecl, TaskEffectFlag, TemplateTermDecl, TypeConditionRestriction, ValidateDecl } from "../ast/assembly";
import { ResolvedASCIIStringOfEntityAtomType, ResolvedAtomType, ResolvedConceptAtomType, ResolvedConceptAtomTypeEntry, ResolvedOkEntityAtomType, ResolvedErrEntityAtomType, ResolvedSomethingEntityAtomType, ResolvedMapEntryEntityAtomType, ResolvedEntityAtomType, ResolvedEnumEntityAtomType, ResolvedEphemeralListType, ResolvedFunctionType, ResolvedHavocEntityAtomType, ResolvedListEntityAtomType, ResolvedMapEntityAtomType, ResolvedObjectEntityAtomType, ResolvedPathEntityAtomType, ResolvedPathFragmentEntityAtomType, ResolvedPathGlobEntityAtomType, ResolvedPathValidatorEntityAtomType, ResolvedPrimitiveInternalEntityAtomType, ResolvedQueueEntityAtomType, ResolvedRecordAtomType, ResolvedSetEntityAtomType, ResolvedStackEntityAtomType, ResolvedStringOfEntityAtomType, ResolvedTaskAtomType, ResolvedTupleAtomType, ResolvedType, ResolvedTypedeclEntityAtomType, ResolvedValidatorEntityAtomType, TemplateBindScope, ResolvedFunctionTypeParam, ResolvedInternalEntityAtomType, ResolvedConstructableEntityAtomType, ResolvedPrimitiveCollectionEntityAtomType } from "./resolved_type";
import { AccessEnvValue, AccessFormatInfo, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionExpression, ConstantExpressionValue, ConstructorEphemeralValueList, ConstructorPCodeExpression, ConstructorPrimaryExpression, ConstructorRecordExpression, ConstructorTupleExpression, Expression, LiteralASCIIStringExpression, LiteralASCIITemplateStringExpression, LiteralASCIITypedStringExpression, LiteralBoolExpression, LiteralFloatPointExpression, LiteralIntegralExpression, LiteralNoneExpression, LiteralNothingExpression, LiteralRationalExpression, LiteralRegexExpression, LiteralStringExpression, LiteralTemplateStringExpression, LiteralTypedPrimitiveConstructorExpression, LiteralTypedStringExpression, PCodeInvokeExpression, SpecialConstructorExpression } from "../ast/body";
import { TIRAccessEnvValue, TIRAccessNamespaceConstantExpression, TIRAccessConstMemberFieldExpression, TIRAccessVariableExpression, TIRExpression, TIRInvalidExpression, TIRLiteralASCIIStringExpression, TIRLiteralASCIITemplateStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression, TIRLiteralStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralTypedPrimitiveConstructorExpression, TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedStringExpression, TIRLiteralValue, TIRCoerceExpression, TIRCoerceSafeExpression, TIRConstructorPrimaryDirectExpression, TIRSpecialConstructorExpression, TIRMapEntryConstructorExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorListExpression, TIRConstructorMapExpression, TIRConstructorTupleExpression, TIRConstructorRecordExpression, TIRConstructorEphemeralValueList, TIRCodePack, TIRTypedeclDirectExpression, TIRTypedeclConstructorExpression, TIRCallNamespaceFunctionExpression, TIRCallNamespaceFunctionWithChecksExpression } from "../tree_ir/tir_body";
import { AndTypeSignature, AutoTypeSignature, EphemeralListTypeSignature, FunctionTypeSignature, NominalTypeSignature, ParseErrorTypeSignature, ProjectTypeSignature, RecordTypeSignature, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature } from "../ast/type";
import { FlowTypeTruthOps, ExpressionTypeEnvironment, VarInfo, FlowTypeTruthValue } from "./type_environment";

import { BSQRegex } from "../bsqregex";
import { extractLiteralStringValue, extractLiteralASCIIStringValue, SourceInfo } from "../build_decls";
import { TIRASCIIStringOfEntityType, TIRConceptSetType, TIRConceptType, TIREntityType, TIREnumEntityType, TIREphemeralListType, TIRErrEntityType, TIRFieldKey, TIRHavocEntityType, TIRInvariantDecl, TIRInvokeKey, TIRListEntityType, TIRMapEntityTIRType, TIRMapEntryEntityType, TIRMemberConstKey, TIRMemberFieldDecl, TIRNamespaceMemberName, TIRObjectEntityType, TIROkEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRSomethingEntityType, TIRStackEntityType, TIRStringOfEntityType, TIRTaskEffectFlag, TIRTaskEnvironmentEffect, TIRTaskResourceEffect, TIRTaskType, TIRTupleType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRTypeMemberName, TIRTypeName, TIRUnionType, TIRValidateDecl, TIRValidatorEntityType } from "../tree_ir/tir_assembly";

const NAT_MAX = 9223372036854775807n; //Int <-> Nat conversions are always safe (for non-negative values)

const INT_MAX = 9223372036854775807n;
const INT_MIN = -INT_MAX; //negation is always safe

class TypeError extends Error {
    readonly file: string;
    readonly line: number;

    constructor(file: string, line: number, message?: string) {
        super(`Type error on ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);

        this.file = file;
        this.line = line;
    }
}

class OOMemberLookupInfo<T> {
    readonly ttype: ResolvedType;
    readonly ootype: OOPTypeDecl;
    readonly oobinds: Map<string, ResolvedType>;
    readonly decl: T;

    constructor(ttype: ResolvedType, ootype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, decl: T) {
        this.ttype = ttype;
        this.ootype = ootype;
        this.oobinds = oobinds;
        this.decl = decl;
    }
}

class OOMemberResolution<T> {
    readonly decl: OOMemberLookupInfo<T>; //should be a unique declaration of the member
    readonly impl: OOMemberLookupInfo<T>[]; //may be no candidates for the actual implementation (then this is a virtual call)
    readonly totalimpls: boolean; //true if every option resolved to an implementation (false if some resolutions didn't find a concrete implementation)

    constructor(decl: OOMemberLookupInfo<T>, impl: OOMemberLookupInfo<T>[], istotal: boolean) {
        this.decl = decl;
        this.impl = impl;
        this.totalimpls = istotal;
    }
}

enum ResolveResultFlag {
    notfound,
    failure
}

class TIRInvokeIDGenerator {
    static generateInvokeIDForInvariant(ttype: TIRTypeKey, invidx: number): TIRInvokeKey {
        return `invariant_${ttype}$${invidx}`;
    }

    static generateInvokeIDForValidate(ttype: TIRTypeKey, invidx: number): TIRInvokeKey {
        return `validate_${ttype}$${invidx}`;
    }

    static generateInvokeIDForConstExp(): TIRInvokeKey {
        xxxx;
    }

    static generateInvokeIDForPreCondition(): TIRInvokeKey {
        xxxx;
    }

    static generateInvokeIDForPostCondition(): TIRInvokeKey {
        xxxx;
    }

    static generateInvokeIDForExportableMethodMember(ttype: TIRTypeKey, name: string): TIRInvokeKey {
        return `method_${ttype}$${name}`;
    }

    static generateInvokeIDForExportableStaticMember(ttype: TIRTypeKey, name: string): TIRInvokeKey {
        return `function_${ttype}$${name}`;
    }

    static generateInvokeIDForNamespaceFunction(ns: string, name: string, terms: string[]): TIRInvokeKey {
        return xxxx;
    }
}

class TIRMemberIDGenerator {
    static generateDefaultMemberID(typeid: string, dname: string): TIRMemberConstKey {
        return `${typeid}$${dname}`;
    }

    static generateMemberConstID(typeid: string, fname: string): TIRFieldKey {
        return `${typeid}$${fname}`;
    }

    static generateMemberFieldID(typeid: string, fname: string): TIRFieldKey {
        return `${typeid}$${fname}`;
    }

    static generateNamespaceConstID(ns: string, cname: string): TIRFieldKey {
        return `${ns}$${cname}`;
    }
}

class TypeChecker {
    private readonly m_assembly: Assembly;
    private m_buildLevel: BuildLevel;

    private m_file: string;
    private m_isTaskFile: boolean;
    private m_errors: [string, number, string][];

    private readonly m_sortedSrcFiles: {fullname: string, shortname: string}[]; 

    private m_specialTypeMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private m_typedeclResolutions: Map<string, ResolvedType> = new Map<string, ResolvedType>();

    private m_tirTypeMap: Map<string, TIRType> = new Map<string, TIRType>();
    private m_toTIRprocessingstack: ResolvedAtomType[] = [];

    private m_pendingEntityDecls: TIRObjectEntityType[] = [];
    private m_pendingTypedeclDecls: TIRTypedeclEntityType[] = [];
    private m_pendingConceptDecls: TIRConceptType[] = [];
    private m_pendingTaskDecls: TIRTaskType[] = [];

    private m_pendingNamespaceConsts: NamespaceConstDecl[] = [];
    private m_pendingConstMemberDecls: OOMemberLookupInfo<StaticMemberDecl>[] = [];

    constructor(assembly: Assembly, buildlevel: BuildLevel, sortedSrcFiles: {fullname: string, shortname: string}[]) {
        this.m_assembly = assembly;

        this.m_buildLevel = buildlevel;

        this.m_file = "[No File]";
        this.m_isTaskFile = false;
        this.m_errors = [];
        
        this.m_sortedSrcFiles = sortedSrcFiles;
    }

    private raiseError(sinfo: SourceInfo, msg?: string) {
        this.m_errors.push([this.m_file, sinfo.line, msg || "Type error"]);
        throw new TypeError(this.m_file, sinfo.line, msg || "Type error");
    }

    private raiseErrorIf(sinfo: SourceInfo, cond: boolean, msg?: string) {
        if (cond) {
            this.raiseError(sinfo, msg);
        }
    }

    getErrorList(): [string, number, string][] {
        return this.m_errors;
    }

    private generateBodyID(sinfo: SourceInfo, srcFile: string, etag?: string): string {
        //Keep consistent with version in parser!!!
        const sfpos = this.m_sortedSrcFiles.findIndex((entry) => entry.fullname === srcFile);

        return `${this.m_sortedSrcFiles[sfpos].shortname}#k${sfpos}${etag !== undefined ? ("_" + etag) : ""}::${sinfo.line}@${sinfo.pos}`;
    }

    compileTimeReduceConstantExpression(exp: Expression, binds: TemplateBindScope): Expression | undefined {
        if(exp.isCompileTimeInlineValue()) {
            if (exp instanceof LiteralTypedStringExpression) {
                const oftype = this.normalizeTypeOnly(exp.stype, binds);
                const ootype = oftype.tryGetUniqueEntityTypeInfo();
                if (ootype instanceof ResolvedValidatorEntityAtomType) {
                    return exp;
                }
                else {
                    return undefined;
                }
            }
            else if (exp instanceof LiteralASCIITypedStringExpression) {
                const oftype = this.normalizeTypeOnly(exp.stype, binds);
                const ootype = oftype.tryGetUniqueEntityTypeInfo();
                if (ootype instanceof ResolvedValidatorEntityAtomType) {
                    return exp;
                }
                else {
                    return undefined;
                }
            }
            else {
                return exp;
            }
        }
        else if (exp instanceof AccessNamespaceConstantExpression) {
            if (!this.m_assembly.hasNamespace(exp.ns)) {
                return undefined;
            }
            const nsdecl = this.m_assembly.getNamespace(exp.ns);

            if (!nsdecl.consts.has(exp.name)) {
                return undefined;
            }

            const cdecl = nsdecl.consts.get(exp.name) as NamespaceConstDecl;
            return this.compileTimeReduceConstantExpression(cdecl.value.exp, binds);
        }
        else if (exp instanceof AccessStaticFieldExpression) {
            const sfimpl = this.resolveMemberConst(exp.sinfo, this.normalizeTypeOnly(exp.stype, binds), exp.name);
            if(sfimpl === undefined) {
                return undefined;
            }
    
            if(sfimpl.decl.attributes.includes("__enum_type")) {
                return exp;
            }
            else {
                return sfimpl.decl.value !== undefined ? this.compileTimeReduceConstantExpression(sfimpl.decl.value.exp, TemplateBindScope.createBaseBindScope(sfimpl.oobinds)) : undefined;
            }
        }
        else {
            return undefined;
        }
    }

    reduceLiteralValueToCanonicalForm(bodyid: string, exp: Expression, binds: TemplateBindScope): [TIRLiteralValue | undefined, ResolvedType] {
        const cexp = this.compileTimeReduceConstantExpression(exp, binds);
        if(cexp === undefined) {
            return [undefined, ResolvedType.createInvalid()];
        }

        const literalenv = ExpressionTypeEnvironment.createInitialEnvForLiteralEval(bodyid, binds);
        let nexp: ExpressionTypeEnvironment | undefined = undefined;

        if(cexp instanceof AccessStaticFieldExpression) {
            nexp = this.checkAccessStaticField(literalenv, cexp);
        }
        else {
            assert(cexp.isLiteralValueExpression());

            if (cexp instanceof LiteralNoneExpression) {
                nexp = this.checkLiteralNoneExpression(literalenv, cexp);
            }
            else if (cexp instanceof LiteralNothingExpression) {
                nexp = this.checkLiteralNothingExpression(literalenv, cexp);
            }
            else if (cexp instanceof LiteralBoolExpression) {
                nexp = this.checkLiteralBoolExpression(literalenv, cexp);
            }
            else if (cexp instanceof LiteralIntegralExpression) {
                nexp = this.checkLiteralIntegralExpression(literalenv, cexp);
            }
            else if (cexp instanceof LiteralStringExpression) {
                nexp = this.checkLiteralStringExpression(literalenv, cexp);
            }
            else if(cexp instanceof LiteralASCIIStringExpression) {
                nexp = this.checkLiteralASCIIStringExpression(literalenv, cexp);
            }
            else if (cexp instanceof LiteralTypedStringExpression) {
                nexp = this.checkLiteralTypedStringExpression(literalenv, cexp);
            }
            else if (cexp instanceof LiteralASCIITypedStringExpression) {
                nexp = this.checkLiteralASCIITypedStringExpression(literalenv, cexp);
            }
            else if(cexp instanceof LiteralTypedPrimitiveConstructorExpression) {
                nexp = this.checkLiteralTypedPrimitiveConstructorExpression(literalenv, cexp);
            }
            else {
                this.raiseError(exp.sinfo, `Unknown expression kind ${exp.tag} in reduceLiteralValueToCanonicalForm`);

                const iexp = new TIRInvalidExpression(exp.sinfo, "None");
                return [undefined, ResolvedType.createInvalid()];
            }
        }

        const tlit = new TIRLiteralValue(nexp.expressionResult, nexp.expressionResult.expstr); 

        return [tlit, nexp.trepr];
    }

    private setResultExpression(env: ExpressionTypeEnvironment, exp: TIRExpression, trepr: ResolvedType, tinfer: ResolvedType, value: FlowTypeTruthValue | undefined): ExpressionTypeEnvironment {
        assert(this.subtypeOf(tinfer, trepr), `That should be impossible -- ${tinfer.typeID} not subtype of ${trepr.typeID}`);

        let iinfo = env.expInferInfo;
        if(env.expInferInfo.has(exp.expstr)) {
            iinfo = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>(env.expInferInfo).set(exp.expstr, { depvars: new Set<string>(exp.getUsedVars()), infertype: tinfer, infertruth: value || FlowTypeTruthValue.Unknown})
        }
        else {
            const einfo = env.expInferInfo.get(exp.expstr) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue};
            tinfer = einfo.infertype;
            value = einfo.infertruth;
        }

        return env.setResultExpressionInfo(exp, trepr, tinfer, value || FlowTypeTruthValue.Unknown, iinfo);
    }

    private inferExpressionType(env: ExpressionTypeEnvironment, tinfer: ResolvedType, value: FlowTypeTruthValue | undefined): ExpressionTypeEnvironment {
        const iinfo = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>(env.expInferInfo).set(env.expressionResult.expstr, { depvars: new Set<string>(exp.getUsedVars()), infertype: tinfer, infertruth: value || env.etruth});

        return env.setResultExpressionInfo(env.expressionResult, env.trepr, tinfer, value || env.etruth, iinfo);
    }

    private splitConceptTypes(ofc: ResolvedConceptAtomType, withc: ResolvedConceptAtomType): {tp: ResolvedType | undefined, fp: ResolvedType | undefined} {
        if (ofc.typeID === "Any" && withc.typeID === "Some") {
            return { tp: ResolvedType.createSingle(withc), fp: this.getSpecialNoneType() };
        }
        else if (ofc.typeID.startsWith("Option<") && withc.typeID === "ISomething") {
            const somthingres = ResolvedEntityAtomType.create(this.tryGetObjectTypeForFullyResolvedName("Something") as EntityTypeDecl, ofc.conceptTypes[0].binds)
            return { tp: ResolvedType.createSingle(somthingres), fp: this.getSpecialNothingType() };
        }
        else if (ofc.typeID === "IOption" && withc.typeID === "ISomething") {
            return { tp: ResolvedType.createSingle(withc), fp: this.getSpecialNothingType() };
        }
        else {
            xxx; //can we create a new type ofc & withc
            return { tp: ResolvedType.createSingle(withc), fp: ResolvedType.createSingle(ofc) };
        }
    }

    private splitConceptEntityTypes(ofc: ResolvedConceptAtomType, withe: ResolvedEntityAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        const somethingdecl = this.tryGetObjectTypeForFullyResolvedName("Something") as EntityTypeDecl;
        const okdecl = this.tryGetObjectTypeForFullyResolvedName("Result::Ok") as EntityTypeDecl;
        const errdecl = this.tryGetObjectTypeForFullyResolvedName("Result::Err") as EntityTypeDecl;

        //
        //TODO: we may want to handle some ISomething, Something, Option, Nothing situations more precisely if they can arise
        //

        if (ofc.typeID === "Any" && withe.typeID === "None") {
            return { tp: ResolvedType.createSingle(withe), fp: this.getSpecialSomeConceptType() };
        }
        else if (ofc.typeID.startsWith("Option<") && withe.typeID === "Nothing") {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedEntityAtomType.create(somethingdecl, ofc.conceptTypes[0].binds)) };
        }
        else if (ofc.typeID.startsWith("Option<") && withe.typeID === "Something<") {
            return { tp: ResolvedType.createSingle(withe), fp: this.getSpecialNothingType() };
        }
        else if (ofc.typeID.startsWith("Result<") && withe.typeID.startsWith("Result::Ok<")) {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedEntityAtomType.create(errdecl, ofc.conceptTypes[0].binds)) };
        }
        else if (ofc.typeID.startsWith("Result<") && withe.typeID.startsWith("Result::Err<")) {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedEntityAtomType.create(okdecl, ofc.conceptTypes[0].binds)) };
        }
        else if(this.atomSubtypeOf(withe, ofc)) {
            if(ofc.conceptTypes.length === 1 && ofc.conceptTypes[0].concept.attributes.includes("__adt_concept_type")) {
                const splits = [...this.m_objectMap]
                    .filter((tt) => tt[1].terms.length === 0)
                    .map((tt) => ResolvedEntityAtomType.create(tt[1], new Map<string, ResolvedType>()))
                    .filter((tt) => { 
                        const issubtype = this.atomSubtypeOf(tt, ofc);
                        const notwithe = tt.typeID !== withe.typeID;

                        return issubtype && notwithe;
                    });
                
                return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.create(splits) };
            }
            else {
                return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ofc) };
            }
        }
        else {
            return { tp: undefined, fp: ResolvedType.createSingle(ofc) };
        }
    }

    private getConceptsProvidedByTuple(tt: ResolvedTupleAtomType): ResolvedConceptAtomType {
        let tci: ResolvedConceptAtomTypeEntry[] = [...(this.getSpecialTupleConceptType().options[0] as ResolvedConceptAtomType).conceptTypes];

        if (tt.types.every((ttype) => this.subtypeOf(ttype, this.getSpecialAPITypeConceptType()))) {
            tci.push(...(this.getSpecialAPITypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
        }
        else {
            if (tt.types.every((ttype) => this.subtypeOf(ttype, this.getSpecialTestableTypeConceptType()))) {
                tci.push(...(this.getSpecialTestableTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
            }
        }

        return ResolvedConceptAtomType.create(tci);
    }

    private getConceptsProvidedByRecord(rr: ResolvedRecordAtomType): ResolvedConceptAtomType {
        let tci: ResolvedConceptAtomTypeEntry[] = [...(this.getSpecialSomeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes];
        
        if (rr.entries.every((entry) => this.subtypeOf(entry.ptype, this.getSpecialAPITypeConceptType()))) {
            tci.push(...(this.getSpecialAPITypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
        }
        else {
            if (rr.entries.every((entry) => this.subtypeOf(entry.ptype, this.getSpecialTestableTypeConceptType()))) {
                tci.push(...(this.getSpecialTestableTypeConceptType().options[0] as ResolvedConceptAtomType).conceptTypes);
            } 
        }

        return ResolvedConceptAtomType.create(tci);
    }

    private splitConceptTuple(ofc: ResolvedConceptAtomType, witht: ResolvedTupleAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        const withc = this.getConceptsProvidedByTuple(witht);
        if (this.atomSubtypeOf(withc, ofc)) {
            return { tp: ResolvedType.createSingle(witht), fp: ResolvedType.createSingle(ofc) };
        }
        else {
            return { tp: undefined, fp: ResolvedType.createSingle(ofc) };
        }
    }

    private splitConceptRecord(ofc: ResolvedConceptAtomType, withr: ResolvedRecordAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        const withc = this.getConceptsProvidedByRecord(withr);
        if (this.atomSubtypeOf(withc, ofc)) {
            return { tp: ResolvedType.createSingle(withr), fp: ResolvedType.createSingle(ofc) };
        }
        else {
            return { tp: undefined, fp: ResolvedType.createSingle(ofc) };
        }
    }

    private splitAtomTypes(ofa: ResolvedAtomType, witha: ResolvedAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        if (this.atomSubtypeOf(ofa, witha)) {
            return { tp: ResolvedType.createSingle(ofa), fp: undefined };
        }

        if(ofa instanceof ResolvedConceptAtomType) {
            if (witha instanceof ResolvedEntityAtomType) {
                return this.splitConceptEntityTypes(ofa, witha);
            }
            else if(witha instanceof ResolvedConceptAtomType) {
                return this.splitConceptTypes(ofa, witha);
            }
            else if (witha instanceof ResolvedTupleAtomType) {
                return this.splitConceptTuple(ofa, witha);
            }
            else if (witha instanceof ResolvedRecordAtomType) {
                return this.splitConceptRecord(ofa, witha);
            }
            else {
                return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
            }
        }
        else if (ofa instanceof ResolvedTupleAtomType) {
            if (witha instanceof ResolvedTupleAtomType) {
                if(ofa.typeID === witha.typeID) {
                    return { tp: ResolvedType.createSingle(witha), fp: undefined };
                }
                else {
                    return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
                }
            }
            else {
                return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
            }
        }
        else if (ofa instanceof ResolvedRecordAtomType) {
            if (witha instanceof ResolvedRecordAtomType) {
                if(ofa.typeID === witha.typeID) {
                    return { tp: ResolvedType.createSingle(witha), fp: undefined };
                }
                else {
                    return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
                }
            }
            else {
                return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
            }
        }
        else {
            return { tp: undefined, fp: ResolvedType.createSingle(ofa) };
        }
    }

    private splitAtomWithType(ofa: ResolvedAtomType, witht: ResolvedType): { tp: ResolvedType[], fp: ResolvedType[] } {
        let tp: ResolvedType[] = [];
        let fp: ResolvedType[] = [];
        witht.options
            .map((opt) => this.splitAtomTypes(ofa, opt))
            .forEach((rr) => {
                if(rr.tp !== undefined) {
                    tp.push(rr.tp);
                }
                if(rr.fp !== undefined) {
                    fp.push(rr.fp);
                }
            });

        return { tp: tp, fp: fp };
    }

    splitTypes(oft: ResolvedType, witht: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        if (oft.isEmptyType() || witht.isEmptyType()) {
            return { tp: ResolvedType.createEmpty(), fp: ResolvedType.createEmpty() };
        }

        if (oft.typeID === witht.typeID) {
            return { tp: oft, fp: ResolvedType.createEmpty() };
        }

        const paths = oft.options.map((opt) => this.splitAtomWithType(opt, witht));
        let tp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.tp));
        let fp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.fp));

        return {tp: this.typeUpperBound(tp), fp: this.typeUpperBound(fp)};
    }

    getDerivedTypeProjection(fromtype: ResolvedType, oftype: ResolvedType): ResolvedType {
        if(oftype.typeID === "Some") {
            return this.splitTypes(fromtype, this.getSpecialNoneType()).fp;
        }
        else if(oftype.typeID === "IOptionT") {
            if(oftype.options.length === 1 && oftype.typeID.startsWith("Option<")) {
                return (oftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("T") as ResolvedType;
            }
            else {
                return ResolvedType.createInvalid();
            }
        }
        else if(oftype.typeID === "IResultT") {
            if(oftype.options.length === 1 && oftype.typeID.startsWith("Result<")) {
                return (oftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("T") as ResolvedType;
            }
            else {
                return ResolvedType.createInvalid();
            }
        }
        else if(oftype.typeID === "IResultE") {
            if(oftype.options.length === 1 && oftype.typeID.startsWith("Result<")) {
                return (oftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds.get("E") as ResolvedType;
            }
            else {
                return ResolvedType.createInvalid();
            }
        }
        else {
            return ResolvedType.createInvalid();
        }
    }

    private computeBaseTypeForTypeDecl(sinfo: SourceInfo, oftype: ResolvedType, expandstack: string[]): ResolvedPrimitiveInternalEntityAtomType | undefined{
        let oftypeatom = oftype.tryGetUniqueEntityTypeInfo();
        if(oftypeatom === undefined) {
            return undefined;
        }

        if (oftypeatom instanceof ResolvedPrimitiveInternalEntityAtomType) {
            return oftypeatom;
        }
        else if (oftypeatom instanceof ResolvedStringOfEntityAtomType) {
            return this.getSpecialStringType().tryGetUniqueEntityTypeInfo() as ResolvedPrimitiveInternalEntityAtomType;
        }
        else if (oftypeatom instanceof ResolvedASCIIStringOfEntityAtomType) {
            return this.getSpecialASCIIStringType().tryGetUniqueEntityTypeInfo() as ResolvedPrimitiveInternalEntityAtomType;
        }
        else if (oftypeatom instanceof ResolvedPathEntityAtomType) {
            return this.getSpecialStringType().tryGetUniqueEntityTypeInfo() as ResolvedPrimitiveInternalEntityAtomType;
        }
        else if (oftypeatom instanceof ResolvedPathFragmentEntityAtomType) {
            return this.getSpecialStringType().tryGetUniqueEntityTypeInfo() as ResolvedPrimitiveInternalEntityAtomType;
        }
        else if (oftypeatom instanceof ResolvedPathGlobEntityAtomType) {
            return this.getSpecialStringType().tryGetUniqueEntityTypeInfo() as ResolvedPrimitiveInternalEntityAtomType;
        }
        else if (oftypeatom instanceof ResolvedTypedeclEntityAtomType) {
            //recursive expand
            const uutype = (oftypeatom.object.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;
            const uubinds = oftype.tryGetUniqueEntityBindsInfo();
            if (uubinds === undefined) {
                return undefined;
            }

            const roftype = this.normalizeTypeOnly(uutype, TemplateBindScope.createBaseBindScope(uubinds));
            if(expandstack.includes(roftype.typeID)) {
                return undefined;
            }

            expandstack.push(roftype.typeID);
            const bpatom = this.computeBaseTypeForTypeDecl(sinfo, roftype, expandstack);
            expandstack.pop();

            return bpatom;
        }
    }

    private normalizeType_Template(t: TemplateTypeSignature, binds: TemplateBindScope): ResolvedType {
        const rbind = binds.tryTemplateResolveType(t.name);
        if(rbind !== undefined) {
            return rbind;
        }
        else {
            this.raiseError(t.sinfo, `Could not resolve template type name ${t.name}`);
            return ResolvedType.createInvalid();
        }
    }

    private normalizeType_Nominal(t: NominalTypeSignature, binds: TemplateBindScope, resolvestack: string[]): ResolvedType | ResolvedFunctionType {
        let tresolved: TypeSignature = t;
        let isresolution: boolean = false;
        if(t.terms.length === 0) {
            //could be a typedef so go try to resolve that
            [tresolved, isresolution] = this.resolveTypeDef(t.sinfo, t, resolvestack);
        }

        let rtype: ResolvedType | ResolvedFunctionType = ResolvedType.createInvalid(); 
        if (!(tresolved instanceof NominalTypeSignature)) {
            rtype = this.normalizeTypeGeneral(tresolved, binds);
        }
        else {
            const ttname = (tresolved.nameSpace !== "Core" ? (tresolved.nameSpace + "::") : "") + tresolved.computeResolvedName();

            const fconcept = this.m_assembly.tryGetConceptTypeForFullyResolvedName(ttname);
            if (fconcept !== undefined) {
                this.checkTemplateTypesOnType(t.sinfo, fconcept.terms, binds);
                const bbinds = this.resolveTemplateBinds(t.sinfo, fconcept.terms, t.terms, binds);

                rtype = ResolvedType.createSingle(ResolvedConceptAtomTypeEntry.create(fconcept, bbinds));
            }

            const fobject = this.m_assembly.tryGetObjectTypeForFullyResolvedName(ttname);
            if (fobject !== undefined) {
                let rtypeatom: ResolvedEntityAtomType | undefined = undefined;

                this.checkTemplateTypesOnType(t.sinfo, fobject.terms, binds);
                const bbinds = this.resolveTemplateBinds(t.sinfo, fobject.terms, t.terms, binds);

                if(fobject.attributes.includes("__enum_type")) {
                    rtypeatom = ResolvedEnumEntityAtomType.create(fobject);
                }
                else if (fobject.attributes.includes("__validator_type")) {
                    rtypeatom = ResolvedValidatorEntityAtomType.create(fobject);
                }
                else if (fobject.attributes.includes("__pathvalidator_type")) {
                    rtypeatom = ResolvedPathValidatorEntityAtomType.create(fobject);
                }
                else if (fobject.attributes.includes("__typedprimitive")) {
                    const rrtype = (fobject.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;
                    const oftype = this.normalizeTypeOnly(rrtype, binds);
                    if(!(oftype.tryGetUniqueEntityTypeInfo() as ResolvedEntityAtomType)) {
                        this.raiseError(t.sinfo, `Type ${oftype.typeID} is not an entity type`);
                        return ResolvedType.createInvalid();
                    }
                    
                    const basetype = this.computeBaseTypeForTypeDecl(t.sinfo, oftype, []);
                    if(basetype === undefined) {
                        this.raiseError(t.sinfo, `Type ${oftype.typeID} is not a valid type to use as a typedecl`);
                        return ResolvedType.createInvalid();
                    }

                    rtypeatom = ResolvedTypedeclEntityAtomType.create(fobject, oftype.tryGetUniqueEntityTypeInfo() as ResolvedEntityAtomType, basetype);
                }
                else if(fobject.attributes.includes("__stringof_type")) {
                    const validator = bbinds.get("T");
                    if(validator === undefined || !(validator.tryGetUniqueEntityTypeInfo() instanceof ResolvedValidatorEntityAtomType)) {
                        this.raiseError(t.sinfo, "Missing Validator for StringOf");
                        return ResolvedType.createInvalid();
                    }

                    rtypeatom = ResolvedStringOfEntityAtomType.create(fobject, validator.tryGetUniqueEntityTypeInfo() as ResolvedValidatorEntityAtomType);
                }
                else if(fobject.attributes.includes("__asciistringof_type")) {
                    const validator = bbinds.get("T");
                    if(validator === undefined || !(validator.tryGetUniqueEntityTypeInfo() instanceof ResolvedValidatorEntityAtomType)) {
                        this.raiseError(t.sinfo, "Missing Validator for ASCIIStringOf");
                        return ResolvedType.createInvalid();
                    }

                    rtypeatom = ResolvedASCIIStringOfEntityAtomType.create(fobject, validator.tryGetUniqueEntityTypeInfo() as ResolvedValidatorEntityAtomType);
                }
                else if (fobject.attributes.includes("__path_type")) {
                    const pvalidator = bbinds.get("T");
                    if(pvalidator === undefined || !(pvalidator.tryGetUniqueEntityTypeInfo() instanceof ResolvedPathValidatorEntityAtomType)) {
                        this.raiseError(t.sinfo, "Missing Validator for Path");
                        return ResolvedType.createInvalid();
                    }

                    rtypeatom = ResolvedPathEntityAtomType.create(fobject, pvalidator.tryGetUniqueEntityTypeInfo() as ResolvedPathValidatorEntityAtomType);
                }
                else if (fobject.attributes.includes("__pathfragment_type")) {
                    const pvalidator = bbinds.get("T");
                    if(pvalidator === undefined || !(pvalidator.tryGetUniqueEntityTypeInfo() instanceof ResolvedPathValidatorEntityAtomType)) {
                        this.raiseError(t.sinfo, "Missing Validator for PathFragment");
                        return ResolvedType.createInvalid();
                    }

                    rtypeatom = ResolvedPathFragmentEntityAtomType.create(fobject, pvalidator.tryGetUniqueEntityTypeInfo() as ResolvedPathValidatorEntityAtomType);
                }
                else if (fobject.attributes.includes("__pathglob_type")) {
                    const pvalidator = bbinds.get("T");
                    if(pvalidator === undefined || !(pvalidator.tryGetUniqueEntityTypeInfo() instanceof ResolvedPathValidatorEntityAtomType)) {
                        this.raiseError(t.sinfo, "Missing Validator for PathFragment");
                        return ResolvedType.createInvalid();
                    }

                    rtypeatom = ResolvedPathGlobEntityAtomType.create(fobject, pvalidator.tryGetUniqueEntityTypeInfo() as ResolvedPathValidatorEntityAtomType);
                }
                else if (fobject.attributes.includes("__ok_type")) {
                    assert(bbinds.has("T"), "Missing template binding");

                    rtypeatom = ResolvedOkEntityAtomType.create(fobject, bbinds.get("T") as ResolvedType, bbinds.get("E") as ResolvedType);
                }
                else if (fobject.attributes.includes("__err_type")) {
                    assert(bbinds.has("E"), "Missing template binding");
                    
                    rtypeatom = ResolvedErrEntityAtomType.create(fobject, bbinds.get("T") as ResolvedType, bbinds.get("E") as ResolvedType);
                }
                else if (fobject.attributes.includes("__something_type")) {
                    assert(bbinds.has("T"), "Missing template binding");
                    
                    rtypeatom = ResolvedSomethingEntityAtomType.create(fobject, bbinds.get("T") as ResolvedType);
                }
                else if (fobject.attributes.includes("__mapentry_type")) {
                    assert(bbinds.has("K"), "Missing template binding");
                    assert(bbinds.has("V"), "Missing template binding");

                    rtypeatom = ResolvedMapEntryEntityAtomType.create(fobject, bbinds.get("K") as ResolvedType, bbinds.get("V") as ResolvedType);
                }
                else if (fobject.attributes.includes("__havoc_type")) {
                    rtypeatom = ResolvedHavocEntityAtomType.create(fobject);
                }
                else if (fobject.attributes.includes("__list_type")) {
                    assert(bbinds.has("T"), "Missing template binding");

                    rtypeatom = ResolvedListEntityAtomType.create(fobject, bbinds.get("T") as ResolvedType);
                }
                else if (fobject.attributes.includes("__stack_type")) {
                    assert(bbinds.has("T"), "Missing template binding");

                    rtypeatom = ResolvedStackEntityAtomType.create(fobject, bbinds.get("T") as ResolvedType);
                }
                else if (fobject.attributes.includes("__queue_type")) {
                    assert(bbinds.has("T"), "Missing template binding");

                    rtypeatom = ResolvedQueueEntityAtomType.create(fobject, bbinds.get("T") as ResolvedType);
                }
                else if (fobject.attributes.includes("__set_type")) {
                    assert(bbinds.has("T"), "Missing template binding");

                    rtypeatom = ResolvedSetEntityAtomType.create(fobject, bbinds.get("T") as ResolvedType);
                }
                else if (fobject.attributes.includes("__map_type")) {
                    assert(bbinds.has("K"), "Missing template binding");
                    assert(bbinds.has("V"), "Missing template binding");

                    rtypeatom = ResolvedMapEntityAtomType.create(fobject, bbinds.get("K") as ResolvedType, bbinds.get("V") as ResolvedType);
                }
                else if(fobject.attributes.includes("__typebase")) {
                    //class representing all the primitive values (Int, Bool, String, ...). ALl of these are special implemented values
                    rtypeatom = ResolvedPrimitiveInternalEntityAtomType.create(fobject);
                }
                else {
                    rtypeatom = ResolvedObjectEntityAtomType.create(fobject, bbinds);
                }

                rtype = rtypeatom !== undefined ? ResolvedType.createSingle(rtypeatom) : ResolvedType.createInvalid();
            }

            const ftask = this.m_assembly.tryGetTaskTypeForFullyResolvedName(ttname);
            if (ftask !== undefined) {
                this.checkTemplateTypesOnType(t.sinfo, ftask.terms, binds);
                const bbinds = this.resolveTemplateBinds(t.sinfo, ftask.terms, t.terms, binds);

                rtype = ResolvedType.createSingle(ResolvedTaskAtomType.create(ftask, bbinds));
            }
        }

        if(isresolution) {
            let sstr = (t.nameSpace !== "Core" ? (t.nameSpace + "::") : "") + t.computeResolvedName();

            if(t.terms.length !== 0) {
                sstr += "<" + t.terms.map((t) => this.normalizeTypeOnly(t, binds).typeID).join(", ") + ">";
            }

            this.m_typedeclResolutions.set(sstr, rtype as ResolvedType);
        }

        return rtype;
    }


    private normalizeType_Tuple(t: TupleTypeSignature, binds: TemplateBindScope): ResolvedType {
        const entries = t.entries.map((entry) => this.normalizeTypeOnly(entry, binds));
        return ResolvedType.createSingle(ResolvedTupleAtomType.create(entries));
    }

    private normalizeType_Record(t: RecordTypeSignature, binds: TemplateBindScope): ResolvedType {
        let seenNames = new Set<string>();
        let entries: {pname: string, ptype: ResolvedType}[] = [];
        for (let i = 0; i < t.entries.length; ++i) {
            if (seenNames.has(t.entries[i][0])) {
                //TODO: better error reporting
                return ResolvedType.createInvalid();
            }

            entries.push({pname: t.entries[i][0], ptype: this.normalizeTypeOnly(t.entries[i][1], binds)});
        }

        return ResolvedType.createSingle(ResolvedRecordAtomType.create(entries));
    }

    private normalizeType_EphemeralList(t: EphemeralListTypeSignature, binds: TemplateBindScope): ResolvedType {
        const entries = t.entries.map((entry) => this.normalizeTypeOnly(entry, binds));
        return ResolvedType.createSingle(ResolvedEphemeralListType.create(entries));
    }

    private normalizeType_Projection(t: ProjectTypeSignature, binds: TemplateBindScope): ResolvedType {
        const fromt = this.normalizeTypeOnly(t.fromtype, binds);
        const oft = this.normalizeTypeOnly(t.oftype, binds);

        if(fromt.isInvalidType() || oft.isInvalidType()) {
            return ResolvedType.createInvalid();
        }

        return this.getDerivedTypeProjection(fromt, oft);
    }

    private normalizeType_And(t: AndTypeSignature, binds: TemplateBindScope): ResolvedType {
        const andtypes = t.types.map((opt) => this.normalizeTypeOnly(opt, binds));
        if (andtypes.some((opt) => opt.isInvalidType())) {
            return ResolvedType.createInvalid();
        }

        const ntypes: ResolvedAtomType[][] = andtypes.map((att) => att.options);
        const flattened: ResolvedAtomType[] = ([] as ResolvedAtomType[]).concat(...ntypes);

        if (flattened.some((ttype) => !(ttype instanceof ResolvedConceptAtomType))) {
            //TODO: better error reporting
            return ResolvedType.createInvalid();
        }

        const ctypes = flattened.map((arg) => (arg as ResolvedConceptAtomType).conceptTypes);
        const itypes = (([] as ResolvedConceptAtomTypeEntry[]).concat(...ctypes)).sort((cte1, cte2) => cte1.typeID.localeCompare(cte2.typeID));

        //do a simplification based on A & B when A \Subtypeeq B is A
        let simplifiedTypes: ResolvedConceptAtomTypeEntry[] = [];
        for (let i = 0; i < itypes.length; ++i) {
            let docopy = true;
            for (let j = 0; j < itypes.length; ++j) {
                if (i === j) {
                    continue; //ignore check on same element
                }

                //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Tj
                if (this.atomSubtypeOf(ResolvedConceptAtomType.create([itypes[j]]), ResolvedConceptAtomType.create([itypes[i]]))) {
                    docopy = (itypes[i].typeID === itypes[j].typeID) && i < j; //if same type only keep one copy
                    break;
                }
            }

            if (docopy) {
                simplifiedTypes.push(itypes[i]);
            }
        }

        return ResolvedType.createSingle(ResolvedConceptAtomType.create(simplifiedTypes));
    }

    private normalizeType_Union(t: UnionTypeSignature, binds: TemplateBindScope): ResolvedType {
        const uniontypes = t.types.map((opt) => this.normalizeTypeOnly(opt, binds));

        if (uniontypes.some((opt) => opt.isInvalidType())) {
            return ResolvedType.createInvalid();
        }

        return this.normalizeUnionList(uniontypes);
    }

    private normalizeEphemerals(ephemerals: ResolvedEphemeralListType[]): ResolvedEphemeralListType | undefined {
        const lidx = Math.max(...ephemerals.map((tt) => tt.types.length));
        const uidx = Math.min(...ephemerals.map((tt) => tt.types.length));
        if(lidx !== uidx) {
            return undefined; //can't have different lengths!!!
        }

        let nte: ResolvedType[] = [];
        for (let i = 0; i < lidx; ++i) {
            const ttypes = ephemerals.map((tt) => tt.types[i]);
            const ttype = this.typeUpperBound(ttypes);
            if(ephemerals.some((tt) => !tt.types[i].isSameType(ttype))) {
                return undefined; //can't have different types
            }

            nte.push(ttype);
        }

        return ResolvedEphemeralListType.create(nte);
    }

    private normalizeUnionList(types: ResolvedType[]): ResolvedType {
        //flatten any union types
        const ntypes: ResolvedAtomType[][] = types.map((opt) => opt.options);
        let flattened: ResolvedAtomType[] = ([] as ResolvedAtomType[]).concat(...ntypes);

        //check for Some | None and add Any if needed
        if (flattened.some((atom) => atom.typeID === "None") && flattened.some((atom) => atom.typeID === "Some")) {
            flattened.push(this.getSpecialAnyConceptType().options[0]);
        }

        //check for Something<T> | Nothing and add Option<T> if needed
        if (flattened.some((atom) => atom.typeID === "Nothing") && flattened.some((atom) => atom instanceof ResolvedSomethingEntityAtomType)) {
            const copt = this.m_assembly.tryGetConceptTypeForFullyResolvedName("Option") as ConceptTypeDecl;

            const nopts = flattened
                .filter((atom) => atom instanceof ResolvedSomethingEntityAtomType)
                .map((atom) => ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(copt, (atom as ResolvedEntityAtomType).getBinds())]));

            flattened.push(...nopts);
        }

        //check for Ok<T, E> | Err<T, E> and add Result<T> if needed
        if (flattened.some((atom) => atom instanceof ResolvedOkEntityAtomType) && flattened.some((atom) => atom instanceof ResolvedErrEntityAtomType)) {
            const ropt = this.m_assembly.tryGetConceptTypeForFullyResolvedName("Result") as ConceptTypeDecl;

            const okopts =  flattened.filter((atom) => atom instanceof ResolvedOkEntityAtomType);
            const erropts =  flattened.filter((atom) => atom instanceof ResolvedErrEntityAtomType);

            const bothopts = okopts.filter((okatom) => erropts.some((erratom) => {
                const okbinds = (okatom as ResolvedEntityAtomType).getBinds();
                const errbinds = (erratom as ResolvedEntityAtomType).getBinds();
                return (okbinds.get("T") as ResolvedType).typeID === (errbinds.get("T") as ResolvedType).typeID && (okbinds.get("E") as ResolvedType).typeID === (errbinds.get("E") as ResolvedType).typeID;
            }));

            const nopts = bothopts.map((atom) => ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(ropt, (atom as ResolvedEntityAtomType).getBinds())]));

            flattened.push(...nopts);
        }

        const teph = flattened.filter((tt) => tt instanceof ResolvedEphemeralListType) as ResolvedEphemeralListType[];
        let merged = flattened.filter((tt) => !(tt instanceof ResolvedEphemeralListType));

        if (teph.length !== 0) {
            const eet = this.normalizeEphemerals(teph);
            if (eet === undefined || merged.length !== 0) {
                return ResolvedType.createInvalid();
            }
            else {
                merged.push(eet);
            }
        }

        const utypes = merged.sort((cte1, cte2) => cte1.typeID.localeCompare(cte2.typeID));

        //do a simplification based on A | B when A \Subtypeeq B is B
        let simplifiedTypes: ResolvedAtomType[] = [];
        for (let i = 0; i < utypes.length; ++i) {
            const tt = utypes[i];

            //see if there is a type that is a strict supertype
            if (utypes.some((ott) => ott.typeID !== tt.typeID && this.atomSubtypeOf(tt, ott))) {
                continue;
            }

            //see if this is the first occourence of the type
            const idx = utypes.findIndex((ott) => ott.typeID === tt.typeID);
            if (idx < i) {
                continue;
            }

            simplifiedTypes.push(utypes[i]);
        }

        return ResolvedType.create(simplifiedTypes);
    }

    private normalizeType_Function(t: FunctionTypeSignature, binds: TemplateBindScope): ResolvedFunctionType | undefined {
        const params = t.params.map((param, idx) => {
            let ttl = this.normalizeTypeGeneral(param.type, binds);
            return new ResolvedFunctionTypeParam(param.name, ttl);
        });
        const rtype = this.normalizeTypeOnly(t.resultType, binds);

        if (params.some((p) => p.type instanceof ResolvedType && p.type.isInvalidType()) || rtype.isInvalidType()) {
            return undefined;
        }

        if(t.isPred && rtype.typeID !== "Bool") {
            return undefined; //pred must have Bool result type
        }

        return ResolvedFunctionType.create(t.isThisRef, t.recursive, params, rtype, t.isPred);
    }

    private getAllOOFields(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, fmap?: Map<string, [ResolvedType, OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>): Map<string, [ResolvedType, OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]> {
        assert(!ooptype.attributes.includes("__constructable"), "Needs to be handled as special case");

        let declfields = fmap || new Map<string, [ResolvedType, OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>]>();

        //Important to do traversal in Left->Right Topmost traversal order
        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        rprovides.forEach((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            declfields = this.getAllOOFields(provide, concept.concept, concept.binds, declfields);
        });

        ooptype.memberFields.forEach((mf) => {
            if (!declfields.has(mf.name)) {
                declfields.set(mf.name, [ttype, ooptype, mf, oobinds]);
            }
        });

        return declfields;
    }

    private getAllInvariantProvidingTypesInherit(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, invprovs?: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] {
        let declinvs: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] = [...(invprovs || [])];

        if (declinvs.find((dd) => dd[0].typeID === ttype.typeID)) {
            return declinvs;
        }

        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        rprovides.forEach((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            declinvs = this.getAllInvariantProvidingTypesInherit(provide, concept.concept, concept.binds, declinvs);
        });


        if (ooptype.invariants.length !== 0 || ooptype.validates.length !== 0) {
            declinvs.push([ttype, ooptype, oobinds]);
        }

        return declinvs;
    }

    private getAllInvariantProvidingTypesTypedecl(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, invprovs?: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] {
        let declinvs: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][] = [...(invprovs || [])];

        if (declinvs.find((dd) => dd[0].typeID === ttype.typeID)) {
            return declinvs;
        }

        if (!(ttype.tryGetUniqueEntityTypeInfo() instanceof ResolvedTypedeclEntityAtomType)) {
            const ccdecl = ttype.tryGetUniqueEntityTypeInfo() as ResolvedTypedeclEntityAtomType;
            const oftype = ResolvedType.createSingle(ccdecl.valuetype);

            declinvs = this.getAllInvariantProvidingTypesTypedecl(oftype, ccdecl.valuetype.object, ccdecl.valuetype.getBinds(), declinvs);
        }

        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        rprovides.forEach((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            declinvs = this.getAllInvariantProvidingTypesInherit(provide, concept.concept, concept.binds, declinvs);
        });

        if ((ooptype.invariants.length !== 0 || ooptype.validates.length !== 0)
            || (ooptype.attributes.includes("__stringof_type") || ooptype.attributes.includes("__asciistringof_type"))
            || (ooptype.attributes.includes("__path_type") || ooptype.attributes.includes("__pathfragment_type") || ooptype.attributes.includes("__pathglob_type"))
        ) {
            declinvs.push([ttype, ooptype, oobinds]);
        }

        return declinvs;
    }

    private entityTypeConstructorHasInvariants(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>): boolean {
        const ccdecls = this.getAllInvariantProvidingTypesInherit(ttype, ooptype, oobinds);
        return ccdecls.some((ccd) => {
            return ccd[1].invariants.some((ii) => isBuildLevelEnabled(ii.level, this.m_buildLevel));
        });
    }

    private typedeclTypeConstructorHasInvariants(ttype: ResolvedType, ooptype: OOPTypeDecl): boolean {
        const ccdecls = this.getAllInvariantProvidingTypesTypedecl(ttype, ooptype, new Map<string, ResolvedType>());
        return ccdecls.some((ccd) => {
            return ccd[1].invariants.some((ii) => isBuildLevelEnabled(ii.level, this.m_buildLevel));
        });
    }

    private typedeclTypeConstructorFromValueHasInvariants(ttype: ResolvedType, ooptype: OOPTypeDecl): boolean {
        const ccdecls = this.getAllInvariantProvidingTypesInherit(ttype, ooptype, new Map<string, ResolvedType>());
        return ccdecls.some((ccd) => {
            return ccd[1].invariants.some((ii) => isBuildLevelEnabled(ii.level, this.m_buildLevel));
        });
    }

    private toTIRTypedeclChecks(ttype: ResolvedType, invdecls: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): { strof: ResolvedType | undefined, pthof: {validator: ResolvedType, kind: "path" | "pathfragment" | "pathglob"} | undefined } {
        const chkvalidxx = invdecls.find((idp) => {
            return idp[1].attributes.includes("__stringof_type") || idp[1].attributes.includes("__asciistringof_type");
        });
        const chkvalid = (chkvalidxx !== undefined) ? (chkvalidxx[2].get("T") as ResolvedType) : undefined;

        const chkpathxx = invdecls.find((idp) => {
            return idp[1].attributes.includes("__path_type") || idp[1].attributes.includes("__pathfragment_type") || idp[1].attributes.includes("__pathglob_type");
        });
        const chkpath = (chkpathxx !== undefined) ? {validator: (chkpathxx[2].get("T") as ResolvedType), kind: (chkpathxx[1].attributes.includes("__path_type") ? "path" : (chkpathxx[1].attributes.includes("__pathfragment_type") ? "pathfragment" : "pathglob")) as "path" | "pathfragment" | "pathglob"} : undefined;

        return { strof: chkvalid, pthof: chkpath };
    }

    private toTIRTypeKey_Atom(rtype: ResolvedAtomType): TIRTypeKey {
        if(this.m_tirTypeMap.has(rtype.typeID)) {
            return (this.m_tirTypeMap.get(rtype.typeID) as TIRType).tkey;
        }

        if(this.m_toTIRprocessingstack.some((se) => se.typeID === rtype.typeID)) {
            return rtype.typeID;
        }
        this.m_toTIRprocessingstack.push(rtype);

        let tirtype: TIRType | undefined =  undefined;
        if(rtype instanceof ResolvedObjectEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, rtype.object.terms.map((term) => this.toTIRTypeKey(rtype.binds.get(term.name) as ResolvedType)));
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createBaseBindScope(rtype.binds)).map((rr) => this.toTIRTypeKey(rr));
           
            const binds = new Map<string, TIRTypeKey>();
            rtype.binds.forEach((rt, tt) => binds.set(tt, this.toTIRTypeKey(rt)));

            tirtype = new TIRObjectEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, binds);
            this.m_pendingEntityDecls.push(tirtype as TIRObjectEntityType);
        }
        else if(rtype instanceof ResolvedEnumEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));
            const enums = rtype.object.staticMembers.map((sm) => sm.name);

            tirtype = new TIREnumEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, enums);
        }
        else if(rtype instanceof ResolvedTypedeclEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));

            const valuetype = this.toTIRTypeKey(ResolvedType.createSingle(rtype.valuetype));
            const representation = this.toTIRTypeKey(ResolvedType.createSingle(rtype.representation));

            const invdecls = this.getAllInvariantProvidingTypesTypedecl(ResolvedType.createSingle(rtype), rtype.object, new Map<string, ResolvedType>());
            const validators = this.toTIRTypedeclChecks(ResolvedType.createSingle(rtype), invdecls);

            const strof = validators.strof !== undefined ? ({vtype: validators.strof.typeID, vre: this.m_assembly.tryGetValidatorForFullyResolvedName(validators.strof.typeID) as BSQRegex}) : undefined;
            const pthof = validators.pthof !== undefined ? ({vtype: validators.pthof.validator.typeID, vpth: this.m_assembly.tryGetPathValidatorForFullyResolvedName(validators.pthof.validator.typeID) as PathValidator, kind: validators.pthof.kind}) : undefined;

            tirtype = new TIRTypedeclEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, valuetype, representation, strof, pthof);
            this.m_pendingTypedeclDecls.push(tirtype as TIRTypedeclEntityType);
        }
        else if(rtype instanceof ResolvedPrimitiveInternalEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));

            tirtype = new TIRPrimitiveInternalEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes);
        }
        else if(rtype instanceof ResolvedValidatorEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));

            tirtype = new TIRValidatorEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, this.m_assembly.tryGetValidatorForFullyResolvedName(rtype.typeID) as BSQRegex);
        }
        else if(rtype instanceof ResolvedStringOfEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));            
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));
            const revalidator = this.m_assembly.tryGetValidatorForFullyResolvedName(rtype.typeID) as BSQRegex;
            
            tirtype = new TIRStringOfEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, validator, revalidator);
        }
        else if(rtype instanceof ResolvedASCIIStringOfEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));
            const revalidator = this.m_assembly.tryGetValidatorForFullyResolvedName(rtype.typeID) as BSQRegex;
            
            tirtype = new TIRASCIIStringOfEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, validator, revalidator);
        }
        else if(rtype instanceof ResolvedPathValidatorEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));

            tirtype = new TIRPathValidatorEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, this.m_assembly.tryGetPathValidatorForFullyResolvedName(rtype.typeID) as PathValidator);
        }
        else if(rtype instanceof ResolvedPathEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));
            const pthvalidator = this.m_assembly.tryGetPathValidatorForFullyResolvedName(rtype.typeID) as PathValidator;
            
            tirtype = new TIRPathEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, validator, pthvalidator);
        }
        else if(rtype instanceof ResolvedPathFragmentEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));
            const pthvalidator = this.m_assembly.tryGetPathValidatorForFullyResolvedName(rtype.typeID) as PathValidator;
            
            tirtype = new TIRPathFragmentEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, validator, pthvalidator);
        }
        else if(rtype instanceof ResolvedPathGlobEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));
            const pthvalidator = this.m_assembly.tryGetPathValidatorForFullyResolvedName(rtype.typeID) as PathValidator;
            
            tirtype = new TIRPathGlobEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, validator, pthvalidator);
        }
        else if(rtype instanceof ResolvedOkEntityAtomType) {
            const typet = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const typee = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet, typee]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createDoubleBindScope("T", rtype.typeT, "E", rtype.typeE)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIROkEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, typee);
        }
        else if(rtype instanceof ResolvedErrEntityAtomType) {
            const typet = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const typee = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet, typee]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createDoubleBindScope("T", rtype.typeT, "E", rtype.typeE)).map((rr) => this.toTIRTypeKey(rr));

            tirtype = new TIRErrEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, typee);
        }
        else if(rtype instanceof ResolvedSomethingEntityAtomType) {
            const typet = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRSomethingEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet);
        }
        else if(rtype instanceof ResolvedMapEntryEntityAtomType) {
            const typet = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeK));
            const typee = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeV));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet, typee]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createDoubleBindScope("K", rtype.typeK, "V", rtype.typeV)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRMapEntryEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, typee);
        }
        else if(rtype instanceof ResolvedHavocEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            tirtype = new TIRHavocEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes);
        }
        else if(rtype instanceof ResolvedListEntityAtomType) {
            const typet = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRListEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet);
        }
        else if(rtype instanceof ResolvedStackEntityAtomType) {
            const typet = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRStackEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet);
        }
        else if(rtype instanceof ResolvedQueueEntityAtomType) {
            const typet = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRQueueEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet);
        }
        else if(rtype instanceof ResolvedSetEntityAtomType) {
            const typet = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeT));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRSetEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet);
        }
        else if(rtype instanceof ResolvedMapEntityAtomType) {
            const typek = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeK));
            const typev = this.toTIRTypeKey(ResolvedType.createSingle(rtype.typeV));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typek, typev]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createDoubleBindScope("K", rtype.typeK, "V", rtype.typeV)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRMapEntityTIRType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typek, typev);
        }
        else if(rtype instanceof ResolvedConceptAtomType) {
            if(rtype.conceptTypes.length === 1) {
                const rconcept = rtype.conceptTypes[0];
                const tname = new TIRTypeName(rconcept.concept.ns, rconcept.concept.name, rconcept.concept.terms.map((term) => this.toTIRTypeKey(rconcept.binds.get(term.name) as ResolvedType)));
                const supertypes = this.resolveProvides(rconcept.concept, TemplateBindScope.createBaseBindScope(rconcept.binds)).map((rr) => this.toTIRTypeKey(rr));
                
                const binds = new Map<string, TIRTypeKey>();
                rconcept.binds.forEach((rt, tt) => binds.set(tt, this.toTIRTypeKey(rt)));

                tirtype = new TIRConceptType(rconcept.typeID, tname, rconcept.concept.sourceLocation, rconcept.concept.srcFile, rconcept.concept.attributes, supertypes, binds);
                this.m_pendingConceptDecls.push(tirtype as TIRConceptType);
            }
            else {
                const tirconjuncts = rtype.conceptTypes.map((cpt) => {
                    return this.toTIRTypeKey(ResolvedType.createSingle(ResolvedConceptAtomType.create([cpt])));
                });

                tirtype = new TIRConceptSetType(rtype.typeID, tirconjuncts);
            }
        }
        else if(rtype instanceof ResolvedTaskAtomType) {
            const tname = new TIRTypeName(rtype.task.ns, rtype.task.name, rtype.task.terms.map((term) => this.toTIRTypeKey(rtype.binds.get(term.name) as ResolvedType)));
            const supertypes = this.resolveProvides(rtype.task, TemplateBindScope.createBaseBindScope(rtype.binds)).map((rr) => this.toTIRTypeKey(rr));

            const binds = new Map<string, TIRTypeKey>();
            rtype.binds.forEach((rt, tt) => binds.set(tt, this.toTIRTypeKey(rt)));

            const mainfunc = {mkey: TIRInvokeIDGenerator.generateInvokeIDForExportableStaticMember(rtype.typeID, rtype.task.mainfunc.name), mname: rtype.task.mainfunc.name};
            const onfuncs = {
                onCanel: rtype.task.onfuncs.onCanel !== undefined ? (TIRInvokeIDGenerator.generateInvokeIDForExportableMethodMember(rtype.typeID, rtype.task.onfuncs.onCanel.name)) : undefined, 
                onFailure: rtype.task.onfuncs.onFailure !== undefined ? (TIRInvokeIDGenerator.generateInvokeIDForExportableMethodMember(rtype.typeID, rtype.task.onfuncs.onFailure.name)) : undefined, 
                onTimeout: rtype.task.onfuncs.onTimeout !== undefined ? (TIRInvokeIDGenerator.generateInvokeIDForExportableMethodMember(rtype.typeID, rtype.task.onfuncs.onTimeout.name)) : undefined, 
            };

            tirtype = new TIRTaskType(rtype.typeID, tname, rtype.task.sourceLocation, rtype.task.srcFile, rtype.task.attributes, supertypes, binds, mainfunc, onfuncs);
            this.m_pendingTaskDecls.push(tirtype as TIRTaskType);
        }
        else if(rtype instanceof ResolvedTupleAtomType) {
            const supertypes = this.getConceptsProvidedByTuple(rtype).conceptTypes.map((cc) => this.toTIRTypeKey(ResolvedType.createSingle(ResolvedConceptAtomType.create([cc]))));
            tirtype = new TIRTupleType(rtype.typeID, rtype.types.map((tt) => this.toTIRTypeKey(tt)), supertypes);
        }
        else if(rtype instanceof ResolvedRecordAtomType) {
            const supertypes = this.getConceptsProvidedByRecord(rtype).conceptTypes.map((cc) => this.toTIRTypeKey(ResolvedType.createSingle(ResolvedConceptAtomType.create([cc]))));
            tirtype = new TIRRecordType(rtype.typeID, rtype.entries.map((entrey) => {
                return {pname: entrey.pname, ptype: this.toTIRTypeKey(entrey.ptype)};
            }), supertypes);
        }
        else {
            tirtype = new TIREphemeralListType(rtype.typeID, (rtype as ResolvedEphemeralListType).types.map((tt) => this.toTIRTypeKey(tt)));
        }

        this.m_toTIRprocessingstack.pop();
        this.m_tirTypeMap.set(rtype.typeID, tirtype);

        return rtype.typeID;
    }

    private toTIRTypeKey(rtype: ResolvedType): TIRTypeKey {
        if(this.m_tirTypeMap.has(rtype.typeID)) {
            return (this.m_tirTypeMap.get(rtype.typeID) as TIRType).tkey;
        }

        if(rtype.options.length === 1) {
            return this.toTIRTypeKey_Atom(rtype.options[0]);
        }
        else {
            const opts = rtype.options.map((opt) => this.toTIRTypeKey_Atom(opt));
            const tt = new TIRUnionType(rtype.typeID, opts);
            
            this.m_tirTypeMap.set(rtype.typeID, tt);
            return tt.tkey;
        }
    }

    private atomSubtypeOf_EntityConcept(t1: ResolvedEntityAtomType, t2: ResolvedConceptAtomType): boolean {
        const t2type = ResolvedType.createSingle(t2);

        if(t1.isNothingType() && this.subtypeOf(t2type, this.getSpecialIOptionConceptType())) {
            return true;
        }
        else {
            const t1provides = this.resolveProvides(t1.object, TemplateBindScope.createBaseBindScope(t1.getBinds()));
            return t1provides.some((provide) => this.subtypeOf(provide, t2type));
        }
    }

    private atomSubtypeOf_TupleConcept(t1: ResolvedTupleAtomType, t2: ResolvedConceptAtomType): boolean {
        const tt = this.getConceptsProvidedByTuple(t1);
        return this.subtypeOf(ResolvedType.createSingle(tt), ResolvedType.createSingle(t2));
    }

    private atomSubtypeOf_RecordConcept(t1: ResolvedRecordAtomType, t2: ResolvedConceptAtomType): boolean {
        const tr = this.getConceptsProvidedByRecord(t1);
        return this.subtypeOf(ResolvedType.createSingle(tr), ResolvedType.createSingle(t2));
    }

    private atomSubtypeOf_ConceptConcept(t1: ResolvedConceptAtomType, t2: ResolvedConceptAtomType, ): boolean {
        return t2.conceptTypes.every((c2t) => {
            return t1.conceptTypes.some((c1t) => {
                if (c1t.concept.ns === c2t.concept.ns && c1t.concept.name === c2t.concept.name) {
                    let allBindsOk = true;
                    c1t.binds.forEach((v, k) => (allBindsOk = allBindsOk && v.typeID === (c2t.binds.get(k) as ResolvedType).typeID));
                    return allBindsOk;
                }

                const t2type = ResolvedType.createSingle(ResolvedConceptAtomType.create([c2t]));
                const c1tprovides = this.resolveProvides(c1t.concept, TemplateBindScope.createBaseBindScope(c1t.binds));

                return c1tprovides.some((provide) => this.subtypeOf(provide, t2type));
            });
        });
    }

    private internSpecialConceptType(name: string, binds?: Map<string, ResolvedType>): ResolvedType {
        if (this.m_specialTypeMap.has(name)) {
            return this.m_specialTypeMap.get(name) as ResolvedType;
        }

        const tconcept = ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(this.m_assembly.tryGetConceptTypeForFullyResolvedName(name) as ConceptTypeDecl, binds || new Map<string, ResolvedType>())]);
        const rtype = ResolvedType.createSingle(tconcept as ResolvedAtomType);
        this.m_specialTypeMap.set(name, rtype);

        return rtype;
    }

    private internSpecialPrimitiveObjectType(name: string): ResolvedType {
        if (this.m_specialTypeMap.has(name)) {
            return this.m_specialTypeMap.get(name) as ResolvedType;
        }

        const tobject = ResolvedPrimitiveInternalEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName(name) as EntityTypeDecl);
        const rtype = ResolvedType.createSingle(tobject as ResolvedAtomType);
        this.m_specialTypeMap.set(name, rtype);

        return rtype;
    }

    getSpecialNoneType(): ResolvedType { return this.internSpecialPrimitiveObjectType("None"); }
    getSpecialBoolType(): ResolvedType { return this.internSpecialPrimitiveObjectType("Bool"); }
    getSpecialIntType(): ResolvedType { return this.internSpecialPrimitiveObjectType("Int"); }
    getSpecialNatType(): ResolvedType { return this.internSpecialPrimitiveObjectType("Nat"); }
    getSpecialBigIntType(): ResolvedType { return this.internSpecialPrimitiveObjectType("BigInt"); }
    getSpecialBigNatType(): ResolvedType { return this.internSpecialPrimitiveObjectType("BigNat"); }
    getSpecialRationalType(): ResolvedType { return this.internSpecialPrimitiveObjectType("Rational"); }
    getSpecialFloatType(): ResolvedType { return this.internSpecialPrimitiveObjectType("Float"); }
    getSpecialDecimalType(): ResolvedType { return this.internSpecialPrimitiveObjectType("Decimal"); }
    getSpecialStringType(): ResolvedType { return this.internSpecialPrimitiveObjectType("String"); }
    getSpecialASCIIStringType(): ResolvedType { return this.internSpecialPrimitiveObjectType("ASCIIString"); }
    getSpecialByteBufferType(): ResolvedType { return this.internSpecialPrimitiveObjectType("ByteBuffer"); }
    getSpecialDateTimeType(): ResolvedType { return this.internSpecialPrimitiveObjectType("DateTime"); }
    getSpecialUTCDateTimeType(): ResolvedType { return this.internSpecialPrimitiveObjectType("UTCDateTime"); }
    getSpecialPlainDateType(): ResolvedType { return this.internSpecialPrimitiveObjectType("PlainDate"); }
    getSpecialPlainTimeType(): ResolvedType { return this.internSpecialPrimitiveObjectType("PlainTime"); }

    getSpecialTickTimeType(): ResolvedType { return this.internSpecialPrimitiveObjectType("TickTime"); }
    getSpecialLogicalTimeType(): ResolvedType { return this.internSpecialPrimitiveObjectType("LogicalTime"); }
    getSpecialISOTimeStampType(): ResolvedType { return this.internSpecialPrimitiveObjectType("ISOTimeStamp"); }
    getSpecialUUID4Type(): ResolvedType { return this.internSpecialPrimitiveObjectType("UUID4"); }
    getSpecialUUID7Type(): ResolvedType { return this.internSpecialPrimitiveObjectType("UUID7"); }
    getSpecialSHAContentHashType(): ResolvedType { return this.internSpecialPrimitiveObjectType("SHAContentHash"); }
    getSpecialLatLongCoordinateType(): ResolvedType { return this.internSpecialPrimitiveObjectType("LatLongCoordinate"); }
    getSpecialRegexType(): ResolvedType { return this.internSpecialPrimitiveObjectType("Regex"); }
    getSpecialNothingType(): ResolvedType { return this.internSpecialPrimitiveObjectType("Nothing"); }

    getSpecialAnyConceptType(): ResolvedType { return this.internSpecialConceptType("Any"); }
    getSpecialSomeConceptType(): ResolvedType { return this.internSpecialConceptType("Some"); }

    getSpecialKeyTypeConceptType(): ResolvedType { return this.internSpecialConceptType("KeyType"); }
    getSpecialValidatorConceptType(): ResolvedType { return this.internSpecialConceptType("Validator"); }
    getSpecialPathValidatorConceptType(): ResolvedType { return this.internSpecialConceptType("PathValidator"); }

    getSpecialTestableTypeConceptType(): ResolvedType { return this.internSpecialConceptType("TestableType"); }
    getSpecialAPITypeConceptType(): ResolvedType { return this.internSpecialConceptType("APIType"); }
    getSpecialTupleConceptType(): ResolvedType { return this.internSpecialConceptType("Tuple"); }
    getSpecialRecordConceptType(): ResolvedType { return this.internSpecialConceptType("Record"); }

    getSpecialISomethingConceptType(): ResolvedType { return this.internSpecialConceptType("ISomething"); }
    getSpecialIOptionConceptType(): ResolvedType { return this.internSpecialConceptType("IOption"); }
    getSpecialIOptionTConceptType(): ResolvedType { return this.internSpecialConceptType("IOptionT"); }

    getSpecialIResultConceptType(): ResolvedType { return this.internSpecialConceptType("IResult"); }
    getSpecialIOkConceptType(): ResolvedType { return this.internSpecialConceptType("IOk"); }
    getSpecialIErrTConceptType(): ResolvedType { return this.internSpecialConceptType("IErr"); }
    getSpecialIResultTConceptType(): ResolvedType { return this.internSpecialConceptType("IResultT"); }
    getSpecialIResultEConceptType(): ResolvedType { return this.internSpecialConceptType("IResultE"); }

    getSpecialObjectConceptType(): ResolvedType { return this.internSpecialConceptType("Object"); }

    getSpecialHavocType(): ResolvedType { return ResolvedType.createSingle(ResolvedHavocEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("HavocSequence") as EntityTypeDecl)); }

    getStringOfType(t: ResolvedValidatorEntityAtomType): ResolvedType { return ResolvedType.createSingle(ResolvedStringOfEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("StringOf") as EntityTypeDecl, t)); }
    getASCIIStringOfType(t: ResolvedValidatorEntityAtomType): ResolvedType { return ResolvedType.createSingle(ResolvedASCIIStringOfEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("ASCIIStringOf") as EntityTypeDecl, t)); }
    
    getSomethingType(t: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedSomethingEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("Something") as EntityTypeDecl, t)); }
    getOkType(t: ResolvedType, e: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedOkEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("Result::Ok") as EntityTypeDecl, t, e)); }
    getErrType(t: ResolvedType, e: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedErrEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("Result::Err") as EntityTypeDecl, t, e)); }

    getOptionConceptType(t: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(this.m_assembly.tryGetConceptTypeForFullyResolvedName("Option") as ConceptTypeDecl, new Map<string, ResolvedType>().set("T", t))])); }
    getResultConceptType(t: ResolvedType, e: ResolvedType): ResolvedType { return ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(this.m_assembly.tryGetConceptTypeForFullyResolvedName("Result") as ConceptTypeDecl, new Map<string, ResolvedType>().set("T", t).set("E", e))])); }
    
    getPathType(t: ResolvedPathValidatorEntityAtomType): ResolvedType { return ResolvedType.createSingle(ResolvedPathEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("Path") as EntityTypeDecl, t)); }
    getPathFragmentType(t: ResolvedPathValidatorEntityAtomType): ResolvedType { return ResolvedType.createSingle(ResolvedPathFragmentEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("PathFragment") as EntityTypeDecl, t)); }
    getPathGlobType(t: ResolvedPathValidatorEntityAtomType): ResolvedType { return ResolvedType.createSingle(ResolvedPathGlobEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("PathGlob") as EntityTypeDecl, t)); }

    ////
    //Type representation, normalization, and operations
    resolveTypeDef(sinfo: SourceInfo, t: NominalTypeSignature, resolvestack: string[]): [TypeSignature, boolean] {
        if (!this.m_assembly.hasNamespace(t.nameSpace)) {
            return [t, false];
        }

        const lname = (t.nameSpace !== "Core" ? (t.nameSpace + "::") : "") + t.tnames.join("::");
        const nsd = this.m_assembly.getNamespace(t.nameSpace);
        if (!nsd.typeDefs.has(lname)) {
            return [t, false];
        }

        if(resolvestack.includes(lname)) {
            //it is a recursive namespace lookup
            this.raiseError(sinfo, `Recursive typedef on ${lname}`);
            return [t, false];
        }

        //compute the bindings to use when resolving the RHS of the typedef alias
        const tresolved = nsd.typeDefs.get(lname) as NamespaceTypedef;
        if (tresolved.boundType instanceof NominalTypeSignature) {
            resolvestack.push(lname);
            return this.resolveTypeDef(sinfo, tresolved.boundType, resolvestack);
        }
        else {
            return [tresolved.boundType, true];
        }
    }

    private resolveTemplateBinds(sinfo: SourceInfo, declterms: TemplateTermDecl[], giventerms: TypeSignature[], binds: TemplateBindScope): Map<string, ResolvedType> {
        let fullbinds = new Map<string, ResolvedType>();

        for (let i = 0; i < declterms.length; ++i) {
            const ttype = this.normalizeTypeOnly(giventerms[i], binds);
            this.raiseErrorIf(sinfo, ttype.isInvalidType(), `Could not resolve template for ${declterms[i].name} given binding as ${giventerms[i].getDiagnosticName()}`)

            fullbinds.set(declterms[i].name, ttype);
        }

        return fullbinds;
    }

    private tryGetMemberImpl_helper<T extends OOMemberDecl>(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberLookupInfo<T>[] | ResolveResultFlag {
        const mdecl = fnlookup(ooptype);
        if(mdecl !== undefined) {
            if(mdecl.hasAttribute("abstract")) {
                return ResolveResultFlag.notfound;
            }
            else {
                return [new OOMemberLookupInfo<T>(ttype, ooptype, oobinds, mdecl)];
            }
        }

        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        if(rprovides.length === 0) {
            return ResolveResultFlag.notfound;
        }

        const options = rprovides.map((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            return this.tryGetMemberImpl_helper<T>(provide, concept.concept, concept.binds, fnlookup);
        })
        .filter((opt) => Array.isArray(opt));

        let impls: OOMemberLookupInfo<T>[] = [];
        for(let i = 0; i < options.length; ++i) {
            const newopts = (options[i] as OOMemberLookupInfo<T>[]).filter((opt) => !impls.some((info) => info.ttype.typeID === opt.ttype.typeID));
            impls.push(...newopts);
        }

        return impls;
    }

    private tryGetMemberDecls_helper<T extends OOMemberDecl>(name: string, ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberLookupInfo<T>[] | ResolveResultFlag {
        const mdecl = fnlookup(ooptype);
        if(mdecl !== undefined) {
            if(mdecl.hasAttribute("abstract") || mdecl.hasAttribute("virtual")) {
                return [new OOMemberLookupInfo<T>(ttype, ooptype, oobinds, mdecl)];
            }
        }

        const rprovides = this.resolveProvides(ooptype, TemplateBindScope.createBaseBindScope(oobinds));
        if(rprovides.length === 0) {
            return ResolveResultFlag.notfound;
        }

        const options = rprovides.map((provide) => {
            const concept = (provide.options[0] as ResolvedConceptAtomType).conceptTypes[0];
            return this.tryGetMemberDecls_helper<T>(name, provide, concept.concept, concept.binds, fnlookup);
        });

        if(options.includes(ResolveResultFlag.failure)) {
            return ResolveResultFlag.failure;
        }

        if(options.includes(ResolveResultFlag.notfound)) {
            if(mdecl === undefined) {
                return ResolveResultFlag.notfound;
            }
            else {
                if(!mdecl.hasAttribute("override")) {
                    return [new OOMemberLookupInfo<T>(ttype, ooptype, oobinds, mdecl)];
                }
                else {
                    this.raiseError(ooptype.sourceLocation, `Found override impl but no virtual/abstract declaration for ${name}`)
                    return ResolveResultFlag.failure;
                }
            }
        }

        let decls: OOMemberLookupInfo<T>[] = [];
        for(let i = 0; i < options.length; ++i) {
            const newopts = (options[i] as OOMemberLookupInfo<T>[]).filter((opt) => !decls.some((info) => info.ttype.typeID === opt.ttype.typeID));
            decls.push(...newopts);
        }

        return decls;
    }

    //When resolving a member on a concept we must find a unique decl and 0 or more implementations
    //const/function/field lookups will assert that an implementation was found -- method/operator lookups may be dynamic and just find a declration
    resolveMemberFromConceptAtom<T extends OOMemberDecl> (sinfo: SourceInfo, ttype: ResolvedType, atom: ResolvedConceptAtomType, name: string, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberResolution<T> | ResolveResultFlag {
        //decls
        const declsopts = atom.conceptTypes
            .map((cpt) => this.tryGetMemberDecls_helper(name, ResolvedType.createSingle(ResolvedConceptAtomType.create([cpt])), cpt.concept, cpt.binds, fnlookup))
            .filter((opt) => opt !== ResolveResultFlag.notfound);

        //Lookup failed
        if(declsopts.some((opt) => opt === ResolveResultFlag.failure)) {
            return ResolveResultFlag.failure;
        }

        let decls: OOMemberLookupInfo<T>[] = [];
        for (let i = 0; i < declsopts.length; ++i) {
            const newopts = (declsopts[i] as OOMemberLookupInfo<T>[]).filter((opt) => !decls.some((info) => info.ttype.typeID === opt.ttype.typeID));
            decls.push(...newopts);
        }

        if (decls.length !== 0) {
            this.raiseError(sinfo, `Cannot resolve ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        if (decls.length > 1) {
            this.raiseError(sinfo, `Multiple declaratons possible for ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        //impls
        const implopts = atom.conceptTypes
            .map((cpt) => this.tryGetMemberImpl_helper(ResolvedType.createSingle(ResolvedConceptAtomType.create([cpt])), cpt.concept, cpt.binds, fnlookup))
            .filter((opt) => opt !== ResolveResultFlag.notfound);

        //Lookup failed
        if(implopts.some((opt) => opt === ResolveResultFlag.failure)) {
            return ResolveResultFlag.failure;
        }

        //ok not to find an implementation

        let impls: OOMemberLookupInfo<T>[] = [];
        for (let i = 0; i < implopts.length; ++i) {
            const newopts = (implopts[i] as OOMemberLookupInfo<T>[]).filter((opt) => !decls.some((info) => info.ttype.typeID === opt.ttype.typeID));
            impls.push(...newopts);
        }

        return new OOMemberResolution<T>(decls[0], impls, impls.length > 0);
    }

    //When resolving a member on an entity we must find a unique decl and a unique or more implementation
    //const/function/field/method lookups will assert that an implementation was found
    resolveMemberFromEntityAtom<T extends OOMemberDecl> (sinfo: SourceInfo, ttype: ResolvedType, atom: ResolvedEntityAtomType, name: string, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberResolution<T> | ResolveResultFlag {
        //decls
        const decls = this.tryGetMemberDecls_helper(name, ResolvedType.createSingle(atom), atom.object, atom.getBinds(), fnlookup);
        
        //Lookup failed
        if(decls === ResolveResultFlag.notfound) {
            this.raiseError(sinfo, `Cannot resolve ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        if(decls === ResolveResultFlag.failure) {
            return ResolveResultFlag.failure;
        }

        if (decls.length > 1) {
            this.raiseError(sinfo, `Multiple declaratons possible for ${name} on type ${atom.typeID}`);
            return ResolveResultFlag.failure;
        }

        //impls
        const impls = this.tryGetMemberImpl_helper(ResolvedType.createSingle(atom), atom.object, atom.getBinds(), fnlookup);

        //Lookup failed
        if(impls === ResolveResultFlag.failure) {
            return ResolveResultFlag.failure;
        }

        return new OOMemberResolution<T>(decls[0], impls !== ResolveResultFlag.notfound ? impls : [], impls !== ResolveResultFlag.notfound);
    }

    resolveMember<T extends OOMemberDecl>(sinfo: SourceInfo, ttype: ResolvedType, name: string, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberResolution<T> | ResolveResultFlag {
        const sopts = ttype.options.map((atom) => {
            if (atom instanceof ResolvedEntityAtomType) {
                return this.resolveMemberFromEntityAtom<T>(sinfo, ResolvedType.createSingle(atom), atom, name, fnlookup);
            }
            else if (atom instanceof ResolvedConceptAtomType) {
                return this.resolveMemberFromConceptAtom<T>(sinfo, ResolvedType.createSingle(atom), atom, name, fnlookup);
            }
            else {
                this.raiseError(sinfo, `Cannot resolve ${name} on type ${atom.typeID}`);
                return ResolveResultFlag.failure;
            }
        });

        if(sopts.some((opt) => opt === ResolveResultFlag.failure)) {
            return ResolveResultFlag.failure;
        }

        let decls: OOMemberLookupInfo<T>[] = [];
        let impls: OOMemberLookupInfo<T>[] = [];
        let totalresolve = true;
        for (let i = 0; i < sopts.length; ++i) {
            const declopt = (sopts[i] as OOMemberResolution<T>).decl;
            const implopts = (sopts[i] as OOMemberResolution<T>).impl;

            if(!decls.some((info) => info.ttype.typeID === declopt.ttype.typeID)) {
                decls.push(declopt);
            }

            const newimpls = implopts.filter((opt) => !impls.some((info) => info.ttype.typeID === opt.ttype.typeID));;
            impls.push(...newimpls);

            totalresolve = totalresolve && (sopts[i] as OOMemberResolution<T>).totalimpls;
        }

        if(decls.length !== 1) {
            this.raiseError(sinfo, `Multiple declaratons possible for ${name} on type ${ttype.typeID}`);
            return ResolveResultFlag.failure;
        }

        return new OOMemberResolution<T>(decls[1], impls, totalresolve);
    }

    resolveMemberConst(sinfo: SourceInfo, ttype: ResolvedType, name: string): OOMemberLookupInfo<StaticMemberDecl> | undefined {
        const resl = this.resolveMember<StaticMemberDecl>(sinfo, ttype, name, (tt: OOPTypeDecl) => tt.staticMembers.find((sm) => sm.name === name));
        if(!(resl instanceof OOMemberResolution<StaticMemberDecl>)) {
            return undefined;
        }

        if(!resl.totalimpls) {
            return undefined;
        }

        if(resl.impl.length !== 1) {
            this.raiseError(sinfo, `Multuple constant values found for ${name} on type ${ttype.typeID} -- ${resl.impl.map((ii) => ii.ttype.typeID).join(", ")}`);
            return undefined;
        }

        return resl.impl[0];
    }

    resolveMemberFunction(sinfo: SourceInfo, ttype: ResolvedType, name: string): OOMemberLookupInfo<StaticFunctionDecl> | undefined {
        const resl = this.resolveMember<StaticFunctionDecl>(sinfo, ttype, name, (tt: OOPTypeDecl) => tt.staticFunctions.find((sf) => sf.name === name));
        if(!(resl instanceof OOMemberResolution<StaticFunctionDecl>)) {
            return undefined;
        }

        if(!resl.totalimpls) {
            return undefined;
        }

        if(resl.impl.length !== 1) {
            this.raiseError(sinfo, `Multuple member function implementations found for ${name} on type ${ttype.typeID} -- ${resl.impl.map((ii) => ii.ttype.typeID).join(", ")}`);
            return undefined;
        }

        return resl.impl[0];
    }

    resolveMemberField(sinfo: SourceInfo, ttype: ResolvedType, name: string, fnlookup: (tt: OOPTypeDecl) => MemberFieldDecl | undefined): OOMemberLookupInfo<MemberFieldDecl> | undefined {
        const resl = this.resolveMember<MemberFieldDecl>(sinfo, ttype, name, (tt: OOPTypeDecl) => tt.memberFields.find((sm) => sm.name === name));
        if(!(resl instanceof OOMemberResolution<MemberFieldDecl>)) {
            return undefined;
        }

        if(!resl.totalimpls) {
            return undefined;
        }

        if(resl.impl.length !== 1) {
            this.raiseError(sinfo, `Multuple member field versions found for ${name} on type ${ttype.typeID} -- ${resl.impl.map((ii) => ii.ttype.typeID).join(", ")}`);
            return undefined;
        }

        return resl.impl[0];
    }

    resolveMemberMethod(sinfo: SourceInfo, ttype: ResolvedType, name: string, argc: number[]): OOMemberResolution<MemberMethodDecl> | undefined {
        const resl = this.resolveMember<MemberMethodDecl>(sinfo, ttype, name, (tt: OOPTypeDecl) => tt.memberMethods.find((mf) => mf.name === name));
        if(!(resl instanceof OOMemberResolution<MemberMethodDecl>)) {
            return undefined;
        }

        return resl;
    }

    normalizeTypeOnly(t: TypeSignature, binds: TemplateBindScope): ResolvedType {
        const res = this.normalizeTypeGeneral(t, binds);
        if (res instanceof ResolvedFunctionType) {
            return ResolvedType.createInvalid();
        }
        else {
            return res;
        }
    }

    normalizeTypeFunction(t: TypeSignature, binds: TemplateBindScope): ResolvedFunctionType | undefined {
        if (t instanceof ParseErrorTypeSignature || t instanceof AutoTypeSignature) {
            return undefined;
        }
        else {
            return this.normalizeType_Function(t as FunctionTypeSignature, binds);
        }
    }

    normalizeTypeGeneral(t: TypeSignature, binds: TemplateBindScope): ResolvedType | ResolvedFunctionType {
        if (t instanceof ParseErrorTypeSignature || t instanceof AutoTypeSignature) {
            return ResolvedType.createInvalid();
        }
        else if (t instanceof FunctionTypeSignature) {
            return this.normalizeTypeFunction(t, binds) || ResolvedType.createInvalid();
        }
        else if (t instanceof TemplateTypeSignature) {
            return this.normalizeType_Template(t, binds);
        }
        else if (t instanceof NominalTypeSignature) {
            return this.normalizeType_Nominal(t, binds, []);
        }
        else if (t instanceof TupleTypeSignature) {
            return this.normalizeType_Tuple(t, binds);
        }
        else if (t instanceof RecordTypeSignature) {
            return this.normalizeType_Record(t, binds);
        }
        else if (t instanceof EphemeralListTypeSignature) {
            return this.normalizeType_EphemeralList(t, binds);
        }
        else if(t instanceof ProjectTypeSignature) {
            return this.normalizeType_Projection(t, binds);
        }
        else if (t instanceof AndTypeSignature) {
            return this.normalizeType_And(t, binds);
        }
        else {
            return this.normalizeType_Union(t as UnionTypeSignature, binds);
        }
    }

    normalizeToNominalRepresentation(t: ResolvedAtomType): ResolvedAtomType {
        if (t instanceof ResolvedTupleAtomType) {
            return this.getSpecialTupleConceptType();
        }
        else if (t instanceof ResolvedRecordAtomType) {
            return this.getSpecialRecordConceptType();
        }
        else {
            return t;
        }
    }

    restrictNone(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialNoneType());
    }

    restrictSome(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialSomeConceptType());
    }

    restrictNothing(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialNothingType());
    }

    restrictSomething(from: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, this.getSpecialISomethingConceptType());
    }

    restrictT(from: ResolvedType, t: ResolvedType): { tp: ResolvedType, fp: ResolvedType } {
        return this.splitTypes(from, t);
    }

    typeUpperBound(types: ResolvedType[]): ResolvedType {
        if(types.length === 0) {
            return ResolvedType.createInvalid();
        }
        else {
            return this.normalizeUnionList(types);
        }
    }

    joinVarInfos(...values: VarInfo[]): VarInfo {
        assert(values.length !== 0);

        const jdef = values.every((vi) => vi.mustDefined);
        const jtype = this.typeUpperBound(values.map((vi) => vi.flowType));
        return new VarInfo(values[0].declaredType, jtype, values[0].isConst, values[0].isCaptured, jdef);
    }

    atomSubtypeOf(t1: ResolvedAtomType, t2: ResolvedAtomType): boolean {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.typeID);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.typeID, new Map<string, boolean>());
            memores = this.m_atomSubtypeRelationMemo.get(t1.typeID) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.typeID);
        if (memoval !== undefined) {
            return memoval;
        }

        let res = false;

        if (t1.typeID === t2.typeID) {
            res = true;
        }
        else if (t1 instanceof ResolvedConceptAtomType && t2 instanceof ResolvedConceptAtomType) {
            res = this.atomSubtypeOf_ConceptConcept(t1, t2);
        }
        else if (t2 instanceof ResolvedConceptAtomType) {
            if (t1 instanceof ResolvedEntityAtomType) {
                res = this.atomSubtypeOf_EntityConcept(t1, t2);
            }
            else if (t1 instanceof ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_TupleConcept(t1, t2);
            }
            else if (t1 instanceof ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_RecordConcept(t1, t2);
            }
            else {
                //fall-through
            }
        }
        else {
            //fall-through
        }

        memores.set(t2.typeID, res);
        return res;
    }

    subtypeOf(t1: ResolvedType, t2: ResolvedType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.typeID);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.typeID, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.typeID) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.typeID);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = (t1.typeID === t2.typeID) || t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));

        memores.set(t2.typeID, res);
        return res;
    }

    resolveProvides(tt: OOPTypeDecl, binds: TemplateBindScope): ResolvedType[] {
        let scpt: [ResolvedConceptAtomTypeEntry, TypeConditionRestriction | undefined][] = [];
        for (let i = 0; i < tt.provides.length; ++i) {
            const rsig = this.normalizeTypeOnly(tt.provides[i][0], binds);
            if(rsig.options.length !== 1 || !(rsig.options[0] instanceof ResolvedConceptAtomType)) {
                this.raiseError(tt.sourceLocation, `provides types must a concept -- got ${rsig.typeID}`);
                return [];
            }

            const flatcpts = rsig.options[0].conceptTypes.map((rcpte) => [rcpte, tt.provides[i][1]] as [ResolvedConceptAtomTypeEntry, TypeConditionRestriction | undefined]);
            scpt.push(...flatcpts)
        }


        let oktypes: ResolvedType[] = [];
        
        for (let i = 0; i < scpt.length; ++i) {
            const rsig = ResolvedType.createSingle(ResolvedConceptAtomType.create([scpt[i][0]]));
            const pcond = scpt[i][1];
            if(pcond === undefined) {
                oktypes.push(rsig);
            }
            else {
                const allok = pcond.constraints.every((consinfo) => {
                    const constype = this.normalizeTypeOnly(consinfo.t, binds)
                    return this.subtypeOf(constype, this.normalizeTypeOnly(consinfo.tconstraint, binds));
                });

                if(allok) {
                    oktypes.push(rsig);
                }
            }
        }

        return oktypes;
    }

    private functionSubtypeOf_helper(t1: ResolvedFunctionType, t2: ResolvedFunctionType): boolean {
        if (t2.isThisRef !== t1.isThisRef) {
            return false; //need to have same ref spec
        }

        if (t2.isPred !== t1.isPred) {
            return false; //need to have same pred spec
        }

        if (t2.params.length !== t1.params.length) {
            return false; //need to have the same number of parameters
        }

        for (let i = 0; i < t2.params.length; ++i) {
            const t2p = t2.params[i];
            const t1p = t1.params[i];
            
            //We want the argument types to be the same for all cases -- no clear reason to overload to more general types
            if (t2p.type instanceof ResolvedFunctionType && t1p.type instanceof ResolvedFunctionType) {
                if (t2p.type.typeID !== t1p.type.typeID) {
                    return false;
                }
            }
            else if (t2p.type instanceof ResolvedType && t1p.type instanceof ResolvedType) {
                if (t2p.type.typeID !== t1p.type.typeID) {
                    return false;
                }
            }
            else {
                return false;
            }

            //check that if t2p is named then t1p has the same name
            if (t2.params[i].name !== "_") {
                if (t2.params[i].name !== t1.params[i].name) {
                    return false;
                }
            }
        }

        if(t1.resultType.typeID !== t2.resultType.typeID) {
            return false;
        }

        return true;
    }

    //Only used for pcode checking
    functionSubtypeOf(t1: ResolvedFunctionType, t2: ResolvedFunctionType): boolean {
        let memores = this.m_subtypeRelationMemo.get(t1.typeID);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.typeID, new Map<string, boolean>());
            memores = this.m_subtypeRelationMemo.get(t1.typeID) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.typeID);
        if (memoval !== undefined) {
            return memoval;
        }

        const res = this.functionSubtypeOf_helper(t1, t2);

        memores.set(t2.typeID, res);
        return res;
    }

    private emitCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        this.raiseErrorIf(sinfo, !this.subtypeOf(env.tinfer, trgttype), `Cannot convert type ${env.tinfer.typeID} into ${trgttype.typeID}`);
        return this.setResultExpression(env, new TIRCoerceSafeExpression(sinfo, env.expressionResult, this.toTIRTypeKey(trgttype)), trgttype, env.tinfer, env.etruth);
    }

    private emitSafeCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        return this.setResultExpression(env, new TIRCoerceSafeExpression(sinfo, env.expressionResult, this.toTIRTypeKey(trgttype)), trgttype, trgttype, env.etruth);
    }

    private checkTemplateTypesOnType(sinfo: SourceInfo, terms: TemplateTermDecl[], typescope: TemplateBindScope) {
        for(let i = 0; i < terms.length; ++i) {
            const terminfo = terms[i];
            const termtype = typescope.templateResolveType(terminfo.name);

            const termconstraint = this.normalizeTypeOnly(terminfo.tconstraint, TemplateBindScope.createEmptyBindScope());
            const boundsok = this.subtypeOf(termtype, termconstraint);
            this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified bounds -- not subtype of ${termconstraint.typeID}`);

            if (terminfo.isunique) {
                this.raiseErrorIf(sinfo, termtype.options.length !== 0 || !ResolvedType.isUniqueType(termtype.options[0]), `Template type ${termtype.typeID} is not unique`);
            }

            if(terminfo.isgrounded) {
                this.raiseErrorIf(sinfo, !ResolvedType.isGroundedType(termtype.options), `Template type ${termtype.typeID} is not grounded`);
            }
        }
    }

    private checkTemplateTypesOnInvoke(sinfo: SourceInfo, terms: TemplateTermDecl[], enclosingscope: TemplateBindScope, binds: Map<string, ResolvedType>, optTypeRestrict?: TypeConditionRestriction) {
        for(let i = 0; i < terms.length; ++i) {
            const terminfo = terms[i];
            const termtype = binds.get(terminfo.name) as ResolvedType;

            const termconstraint = this.normalizeTypeOnly(terminfo.tconstraint, enclosingscope);
            const boundsok = this.subtypeOf(termtype, termconstraint);
            this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified bounds -- not subtype of ${termconstraint.typeID}`);

            if (terminfo.isunique) {
                this.raiseErrorIf(sinfo, termtype.options.length !== 0 || !ResolvedType.isUniqueType(termtype.options[0]), `Template type ${termtype.typeID} is not unique`);
            }

            if(terminfo.isgrounded) {
                this.raiseErrorIf(sinfo, !ResolvedType.isGroundedType(termtype.options), `Template type ${termtype.typeID} is not grounded`);
            }
        }

        if (optTypeRestrict !== undefined) {
            for (let i = 0; i < optTypeRestrict.constraints.length; ++i) {
                const consinfo = optTypeRestrict.constraints[i];
                const constype = this.normalizeTypeOnly(consinfo.t, enclosingscope);

                const constrainttype = this.normalizeTypeOnly(consinfo.tconstraint, enclosingscope);
                const boundsok = this.subtypeOf(constype, constrainttype);
                this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified restriction -- not subtype of ${constrainttype.typeID}`);
            }
        }
    }

    private isPCodeTypedExpression(e: Expression, env: TypeEnvironment): boolean {
        if(e instanceof ConstructorPCodeExpression) {
            return true;
        }
        else if (e instanceof AccessVariableExpression) {
            return env.pcodes.has(e.name);
        }
        else {
            return false;
        }
    }
/*
    private checkInvokeDecl(sinfo: SourceInfo, invoke: InvokeDecl, invokeBinds: Map<string, ResolvedType>, pcodes: PCode[]) {
        this.raiseErrorIf(sinfo, invoke.optRestType !== undefined && invoke.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");

        this.raiseErrorIf(sinfo, invoke.recursive === "no" && pcodes.some((pc) => pc.code.recursive === "yes"), "Recursive decl does not match use");

        const allNames = new Set<string>();
        if (invoke.optRestName !== undefined && invoke.optRestName !== "_") {
            allNames.add(invoke.optRestName);
        }
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
            const rtype = this.m_assembly.normalizeTypeGeneral(invoke.params[i].type, invokeBinds);
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedType && rtype.isEmptyType(), "Bad type signature");
        }

        const firstOptIndex = invoke.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < invoke.params.length; ++i) {
            this.raiseErrorIf(sinfo, !invoke.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }

        if (invoke.optRestType !== undefined) {
            this.resolveAndEnsureTypeOnly(sinfo, invoke.optRestType, invokeBinds);
        }

        const rtype = this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, invokeBinds);
        this.raiseErrorIf(sinfo, rtype.isEmptyType(), "Bad type signature");
    }

    private checkPCodeDecl(sinfo: SourceInfo, fsig: ResolvedFunctionType, rec: "yes" | "no" | "cond", capturedpcodes: PCode[]) {
        this.raiseErrorIf(sinfo, fsig.optRestParamType !== undefined && fsig.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");
        this.raiseErrorIf(sinfo, rec === "no" && fsig.recursive === "yes", "Recursive decl does not match use");
        this.raiseErrorIf(sinfo, fsig.recursive === "no" && capturedpcodes.some((pc) => pc.code.recursive === "yes"), "Recursive decl does not match use");

        const allNames = new Set<string>();
        if (fsig.optRestParamName !== undefined && fsig.optRestParamName !== "_") {
            allNames.add(fsig.optRestParamName);
        }
        for (let i = 0; i < fsig.params.length; ++i) {
            if (fsig.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(fsig.params[i].name), `Duplicate name in invocation signature paramaters "${fsig.params[i].name}"`);
                allNames.add(fsig.params[i].name);
            }
        
            const rtype = fsig.params[i].type;
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedFunctionType, "Cannot have nested function type param");
        }

        const firstOptIndex = fsig.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }

        for (let i = firstOptIndex; i < fsig.params.length; ++i) {
            this.raiseErrorIf(sinfo, !fsig.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }
    }

    private checkValueEq(lhsexp: Expression, lhs: ResolvedType, rhsexp: Expression, rhs: ResolvedType): "err" | "truealways" | "falsealways" | "lhsnone" | "rhsnone" | "lhsnothing" | "rhsnothing" | "lhssomekey" | "rhssomekey" | "stdkey" {
        if (lhsexp instanceof LiteralNoneExpression && rhsexp instanceof LiteralNoneExpression) {
            return "truealways";
        }

        if (lhsexp instanceof LiteralNothingExpression && rhsexp instanceof LiteralNothingExpression) {
            return "truealways";
        }

        if (lhsexp instanceof LiteralNoneExpression) {
            return this.m_assembly.subtypeOf(this.m_assembly.getSpecialNoneType(), rhs) ? "lhsnone" : "falsealways";
        }

        if (rhsexp instanceof LiteralNoneExpression) {
            return this.m_assembly.subtypeOf(this.m_assembly.getSpecialNoneType(), lhs) ? "rhsnone" : "falsealways";
        }

        if (lhsexp instanceof LiteralNothingExpression) {
            return this.m_assembly.subtypeOf(this.m_assembly.getSpecialNothingType(), rhs) ? "lhsnothing" : "falsealways";
        }

        if (rhsexp instanceof LiteralNothingExpression) {
            return this.m_assembly.subtypeOf(this.m_assembly.getSpecialNothingType(), lhs) ? "rhsnothing" : "falsealways";
        }

        //should be a subtype on one of the sides
        if (!this.m_assembly.subtypeOf(lhs, rhs) && !this.m_assembly.subtypeOf(rhs, lhs)) {
            return "err";
        }

        if (lhs.typeID === rhs.typeID) {
            return "stdkey";
        }
        else {
            return this.m_assembly.subtypeOf(lhs, rhs) ? "lhssomekey" : "rhssomekey";
        }
    }

    private getInfoForHasIndex(sinfo: SourceInfo, rtype: ResolvedType, idx: number): "yes" | "no" | "maybe" {
        this.raiseErrorIf(sinfo, rtype.options.some((atom) => !(atom instanceof ResolvedTupleAtomType)), "Can only load indecies from Tuples");

        const yhas = rtype.options.every((atom) => {
            const tatom = atom as ResolvedTupleAtomType;
            return (idx < tatom.types.length);
        });

        const yno = rtype.options.every((atom) => {
            const tatom = atom as ResolvedTupleAtomType;
            return (idx >= tatom.types.length);
        });

        if(yhas) {
            return "yes";
        }
        else if(yno) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    private getInfoForLoadFromSafeIndex(sinfo: SourceInfo, rtype: ResolvedType, idx: number): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasIndex(sinfo, rtype, idx) !== "yes");
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => (atom as ResolvedTupleAtomType).types[idx]));
    }

    private getInfoForLoadFromSafeIndexOnly(sinfo: SourceInfo, rtype: ResolvedType, idx: number): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasIndex(sinfo, rtype, idx) === "no");
        return this.m_assembly.typeUpperBound(rtype.options
            .filter((atom) => (atom as ResolvedTupleAtomType).types.length > idx)
            .map((atom) => (atom as ResolvedTupleAtomType).types[idx])
        );
    }

    private getInfoForHasProperty(sinfo: SourceInfo, rtype: ResolvedType, pname: string): "yes" | "no" | "maybe" {
        this.raiseErrorIf(sinfo, rtype.options.some((atom) => !(atom instanceof ResolvedRecordAtomType)), "Can only load properties from Records");

        const yhas = rtype.options.every((atom) => {
            const tatom = atom as ResolvedRecordAtomType;
            const eidx = tatom.entries.findIndex((entry) => entry.pname === pname);
            return (eidx !== -1);
        });

        const yno = rtype.options.every((atom) => {
            const tatom = atom as ResolvedRecordAtomType;
            const eidx = tatom.entries.findIndex((entry) => entry.pname === pname);
            return (eidx === -1);
        });

        if(yhas) {
            return "yes";
        }
        else if(yno) {
            return "no";
        }
        else {
            return "maybe";
        }
    }

    private getInfoForLoadFromSafeProperty(sinfo: SourceInfo, rtype: ResolvedType, pname: string): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasProperty(sinfo, rtype, pname) !== "yes");
        return this.m_assembly.typeUpperBound(rtype.options.map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.pname === pname) as {pname: string, ptype: ResolvedType}).ptype));
    }

    private getInfoForLoadFromSafePropertyOnly(sinfo: SourceInfo, rtype: ResolvedType, pname: string): ResolvedType {
        this.raiseErrorIf(sinfo, this.getInfoForHasProperty(sinfo, rtype, pname) === "no");
        return this.m_assembly.typeUpperBound(rtype.options
            .filter((atom) => (atom as ResolvedRecordAtomType).entries.find((re) => re.pname === pname) !== undefined)
            .map((atom) => ((atom as ResolvedRecordAtomType).entries.find((re) => re.pname === pname) as {pname: string, ptype: ResolvedType}).ptype)
        );
    }

    private checkPCodeExpression(env: TypeEnvironment, exp: ConstructorPCodeExpression, cbinds: Map<string, ResolvedType>, expectedFunction: ResolvedFunctionType | undefined): PCode {
        this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");

        //TODO: this may capture too many types that are not strictly needed -- maybe want to parse scope track captured types like we do for captured variables
        let bodybinds = new Map<string, ResolvedType>(cbinds);
        env.terms.forEach((ttype, ttname) => {
            if (!bodybinds.has(ttname)) {
                bodybinds.set(ttname, ttype);
            }
        });

        const ltypetry = exp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(exp.invoke.generateSig(), bodybinds);
        this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");

        this.raiseErrorIf(exp.sinfo, exp.invoke.params.length !== (ltypetry as ResolvedFunctionType).params.length, "Mismatch in expected parameter count and provided function parameter count");
        this.raiseErrorIf(exp.sinfo, expectedFunction !== undefined && !this.m_assembly.functionSubtypeOf(ltypetry as ResolvedFunctionType, expectedFunction), "Mismatch in expected and provided function signature");

        let capturedMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();
        let implicitCapturedMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();
        let capturedpcode = new Map<string, PCode>();

        let captures: string[] = [];
        exp.invoke.captureSet.forEach((v) => captures.push(v));
        captures.sort();

        captures.forEach((v) => {
            if (env.pcodes.has(v)) {
                capturedpcode.set(v, env.pcodes.get(v) as PCode);
            }
            else {
                const vinfo = env.lookupVar(v);
                this.raiseErrorIf(exp.sinfo, vinfo === null, `Could not resolve captured variable: ${v}`);
                this.raiseErrorIf(exp.sinfo, (vinfo as VarInfo).declaredType instanceof ResolvedFunctionType, `Cannot capture function typed argument: ${v}`);

                capturedMap.set(v, (vinfo as VarInfo).flowType);
            }
        });


        if(capturedpcode.size !== 0) {
            const cvars = this.m_emitter.flattenCapturedPCodeVarCaptures(capturedpcode);
            cvars.forEach((cv) => implicitCapturedMap.set(cv, (env.lookupVar(cv) as VarInfo).flowType));
        }

        const ikey = MIRKeyGenerator.generatePCodeKey(exp.invoke.isPCodeFn, exp.invoke.bodyID, bodybinds, capturedpcode);
        const cinfo = [
            ...[...capturedMap].sort((a, b) => a[0].localeCompare(b[0])),
            ...[...implicitCapturedMap].sort((a, b) => a[0].localeCompare(b[0]))
        ];

        this.m_emitter.registerPCode(ikey, ikey, exp.invoke, ltypetry as ResolvedFunctionType, bodybinds, cinfo, [...capturedpcode].sort((a, b) => a[0].localeCompare(b[0])));

        return { code: exp.invoke, ikey: ikey, captured: capturedMap, capturedpcode: capturedpcode, ftype: ltypetry as ResolvedFunctionType };
    }
*/

    private checkArgumentList(sinfo: SourceInfo, env: ExpressionTypeEnvironment, args: Expression[], expectedtypes: TypeSignature[], fbinds: TemplateBindScope): TIRExpression[] {
        this.raiseErrorIf(sinfo, args.length !== expectedtypes.length, `call expected ${expectedtypes.length} arguments but got ${args.length}`);
        const eenvs = args.map((arg) => {
            if (/*arg is codepack*/) {
                return xxxx;
            }
            else {
                return this.checkExpression(env, arg, undefined, undefined);
            }
        });

        let cexps: TIRExpression[] = [];
        for (let i = 0; i < eenvs.length; ++i) {
            const oftype = this.normalizeTypeGeneral(expectedtypes[i], fbinds);
            if (oftype instanceof ResolvedType) {
                this.raiseErrorIf(args[i].sinfo, !this.subtypeOf(eenvs[i].tinfer, oftype), `${eenvs[i].tinfer.typeID} is not a subtype of ${oftype.typeID}`);

                cexps.push(this.emitCoerceIfNeeded(eenvs[i], args[i].sinfo, oftype).expressionResult);
            }
            else {
                this.raiseErrorIf(args[i].sinfo, !(eenvs[i].expressionResult instanceof TIRCodePack), "expected a code pack expression");
                this.raiseErrorIf(args[i].sinfo, !this.functionSubtypeOf(eenvs[i].trepr, oftype), `${eenvs[i].trepr.typeID} is not a subtype of ${oftype.typeID}`);

                cexps.push(eenvs[i].expressionResult);
            }
        }
    }

    private hasPreconditions(inv: InvokeDecl): boolean {
        return inv.preconditions.some((cc) => isBuildLevelEnabled(cc.level, this.m_buildLevel));
    }

    private hasPostconditions(inv: InvokeDecl): boolean {
        return inv.postconditions.some((cc) => isBuildLevelEnabled(cc.level, this.m_buildLevel));
    }

    private checkLiteralNoneExpression(env: ExpressionTypeEnvironment, exp: LiteralNoneExpression): ExpressionTypeEnvironment {
        return  this.setResultExpression(env, new TIRLiteralNoneExpression(exp.sinfo), this.getSpecialNoneType(), this.getSpecialNoneType(), undefined);
    }

    private checkLiteralNothingExpression(env: ExpressionTypeEnvironment, exp: LiteralNothingExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralNothingExpression(exp.sinfo), this.getSpecialNothingType(), this.getSpecialNothingType(), undefined);
    }

    private checkLiteralBoolExpression(env: ExpressionTypeEnvironment, exp: LiteralBoolExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralBoolExpression(exp.sinfo, exp.value), this.getSpecialBoolType(), this.getSpecialBoolType(), exp.value ? FlowTypeTruthValue.True : FlowTypeTruthValue.False);
    }

    private checkLiteralIntegralExpression(env: ExpressionTypeEnvironment, exp: LiteralIntegralExpression): ExpressionTypeEnvironment {
        const itype = this.normalizeTypeOnly(exp.itype, env.binds);
        
        if(itype.isSameType(this.getSpecialNatType()) || itype.isSameType(this.getSpecialBigNatType())) {
            this.raiseErrorIf(exp.sinfo, exp.value.startsWith("-"), "Cannot have negative Nat/BigNat literal");
        }

        if(itype.isSameType(this.getSpecialIntType())) {
            const biv = BigInt(exp.value.slice(0, exp.value.length - 1));
            this.raiseErrorIf(exp.sinfo, biv < INT_MIN || INT_MAX < biv, "Constant Int out of valid range");
        }

        if(itype.isSameType(this.getSpecialNatType())) {
            const biv = BigInt(exp.value.slice(0, exp.value.length - 1));
            this.raiseErrorIf(exp.sinfo, NAT_MAX < biv, "Constant Nat out of valid range");
        }

        return this.setResultExpression(env, new TIRLiteralIntegralExpression(exp.sinfo, exp.value, this.toTIRTypeKey(itype)), itype, itype, undefined);
    }

    private checkLiteralRationalExpression(env: ExpressionTypeEnvironment, exp: LiteralRationalExpression): ExpressionTypeEnvironment {
        //TODO: range check here
        return this.setResultExpression(env, new TIRLiteralRationalExpression(exp.sinfo, exp.value), this.getSpecialRationalType(), this.getSpecialRationalType(), undefined);
    } 

    private checkLiteralFloatExpression(env: ExpressionTypeEnvironment, exp: LiteralFloatPointExpression): ExpressionTypeEnvironment {
        const fptype = this.normalizeTypeOnly(exp.fptype, env.binds);

        //TODO: range check here
        return this.setResultExpression(env, new TIRLiteralFloatPointExpression(exp.sinfo, exp.value, this.toTIRTypeKey(fptype)), fptype, fptype, undefined);
    }

    private checkLiteralStringExpression(env: ExpressionTypeEnvironment, exp: LiteralStringExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralStringExpression(exp.sinfo, exp.value), this.getSpecialStringType(), this.getSpecialStringType(), undefined);
    }

    private checkLiteralASCIIStringExpression(env: ExpressionTypeEnvironment, exp: LiteralASCIIStringExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralASCIIStringExpression(exp.sinfo, exp.value), this.getSpecialASCIIStringType(), this.getSpecialASCIIStringType(), undefined);
     }

    private checkLiteralRegexExpression(env: ExpressionTypeEnvironment, exp: LiteralRegexExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralRegexExpression(exp.sinfo, exp.value), this.getSpecialRegexType(), this.getSpecialRegexType(), undefined);
    }

    private checkLiteralTypedStringExpression(env: ExpressionTypeEnvironment, exp: LiteralTypedStringExpression): ExpressionTypeEnvironment {
        const toftype = this.normalizeTypeOnly(exp.stype, env.binds);
        this.raiseErrorIf(exp.sinfo, !(toftype.tryGetUniqueEntityTypeInfo() instanceof ResolvedValidatorEntityAtomType), `Expected Validator for StringOf but got ${toftype.typeID}`);

        const vtype = toftype.tryGetUniqueEntityTypeInfo() as ResolvedValidatorEntityAtomType;
        const stype = ResolvedType.createSingle(ResolvedStringOfEntityAtomType.create(this.m_assembly.getNamespace("Core").objects.get("StringOf") as EntityTypeDecl, vtype));

        const vv = this.m_assembly.tryGetValidatorForFullyResolvedName(toftype.typeID);
        this.raiseErrorIf(exp.sinfo, vv === undefined, `Bad Validator type for StringOf ${toftype.typeID}`);
            
        const argstr = extractLiteralStringValue(exp.value);
        const accepts = (vv as BSQRegex).acceptsString(argstr);
        
        this.raiseErrorIf(exp.sinfo, !accepts, "Literal string failed Validator regex");

        return this.setResultExpression(env, new TIRLiteralTypedStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(stype), this.toTIRTypeKey(toftype)), stype, stype, undefined);
    }

    private checkLiteralASCIITypedStringExpression(env: ExpressionTypeEnvironment, exp: LiteralASCIITypedStringExpression): ExpressionTypeEnvironment {
        const toftype = this.normalizeTypeOnly(exp.stype, env.binds);
        this.raiseErrorIf(exp.sinfo, !(toftype.tryGetUniqueEntityTypeInfo() instanceof ResolvedValidatorEntityAtomType), `Expected Validator for StringOf but got ${toftype.typeID}`);

        const vtype = toftype.tryGetUniqueEntityTypeInfo() as ResolvedValidatorEntityAtomType;
        const stype = ResolvedType.createSingle(ResolvedStringOfEntityAtomType.create(this.m_assembly.getNamespace("Core").objects.get("ASCIIStringOf") as EntityTypeDecl, vtype));

        const vv = this.m_assembly.tryGetValidatorForFullyResolvedName(toftype.typeID);
        this.raiseErrorIf(exp.sinfo, vv === undefined, `Bad Validator type for StringOf ${toftype.typeID}`);
            
        const argstr = extractLiteralASCIIStringValue(exp.value);
        const accepts = (vv as BSQRegex).acceptsString(argstr);
        
        this.raiseErrorIf(exp.sinfo, !accepts, "Literal string failed Validator regex");

        return this.setResultExpression(env, new TIRLiteralASCIITypedStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(stype), this.toTIRTypeKey(toftype)), stype, stype, undefined);
    }

    private checkLiteralTemplateStringExpression(env: ExpressionTypeEnvironment, exp: LiteralTemplateStringExpression): ExpressionTypeEnvironment {
        //
        //TODO: maybe generate special TemplateString<T, K> ... types for these later -- right now we just expect them to be compile inlined
        //
        return this.setResultExpression(env, new TIRLiteralTemplateStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(this.getSpecialStringType())), this.getSpecialStringType(), this.getSpecialStringType(), undefined);
    }

    private checkLiteralASCIITemplateStringExpression(env: ExpressionTypeEnvironment, exp: LiteralASCIITemplateStringExpression): ExpressionTypeEnvironment {
        //
        //TODO: maybe generate special TemplateString<T, K> ... types for these later -- right now we just expect them to be compile inlined
        //
        return this.setResultExpression(env, new TIRLiteralASCIITemplateStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(this.getSpecialASCIIStringType())), this.getSpecialASCIIStringType(), this.getSpecialASCIIStringType(), undefined);
    }

    private checkLiteralTypedPrimitiveConstructorExpression(env: ExpressionTypeEnvironment, exp: LiteralTypedPrimitiveConstructorExpression): ExpressionTypeEnvironment {
        const constype = this.normalizeTypeOnly(exp.constype, env.binds);
        const lexp = this.reduceLiteralValueToCanonicalForm(env.bodyid, exp.value, env.binds);
        this.raiseErrorIf(exp.sinfo, lexp !== undefined, "Not a literal expression");

        this.raiseErrorIf(exp.sinfo, !(constype.tryGetUniqueEntityTypeInfo() instanceof ResolvedTypedeclEntityAtomType), `${constype.typeID} is not a typedecl type`)
        const ccdecl = constype.tryGetUniqueEntityTypeInfo() as ResolvedTypedeclEntityAtomType;

        this.raiseErrorIf(exp.sinfo, ccdecl.representation.typeID !== lexp[1].typeID, `Expected type of ${ccdecl.representation.typeID} (representation type) but got ${lexp[1].typeID}`);

        const tirtypdeclkey = this.toTIRTypeKey(constype);
        const tirtypedecl = this.m_tirTypeMap.get(tirtypdeclkey) as TIRTypedeclEntityType;

        if (tirtypedecl.strvalidator !== undefined) {
            const litval = (lexp[0] as TIRLiteralValue).exp;
            let accepts = false;
            if (litval instanceof TIRLiteralStringExpression) {
                accepts = tirtypedecl.strvalidator.vre.acceptsString(extractLiteralStringValue(litval.expstr));
            }
            else {
                accepts = tirtypedecl.strvalidator.vre.acceptsString(extractLiteralASCIIStringValue(litval.expstr));
            }
            this.raiseErrorIf(exp.sinfo, !accepts, "literal string does not satisfy validator constraint");
        }

        if (tirtypedecl.pthvalidator !== undefined) {
            const litval = (lexp[0] as TIRLiteralValue).exp;
            let accepts = false;
            if (tirtypedecl.pthvalidator.kind === "path") {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPath(extractLiteralStringValue(litval.expstr));
            }
            else if (tirtypedecl.pthvalidator.kind === "pathfragment") {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPathFragment(extractLiteralStringValue(litval.expstr));
            }
            else {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPathGlob(extractLiteralASCIIStringValue(litval.expstr));
            }
            this.raiseErrorIf(exp.sinfo, !accepts, "literal string does not satisfy path validator constraint");
        }

        if (!this.typedeclTypeConstructorHasInvariants(constype, ccdecl.object)) {
            const nexp = new TIRLiteralTypedPrimitiveDirectExpression(exp.sinfo, (lexp[0] as TIRLiteralValue).exp, this.toTIRTypeKey(constype), this.toTIRTypeKey(ResolvedType.createSingle(ccdecl.representation)));
            return this.setResultExpression(env, nexp, constype, constype, undefined);
        }
        else {
            const nexp = new TIRLiteralTypedPrimitiveConstructorExpression(exp.sinfo, (lexp[0] as TIRLiteralValue).exp, this.toTIRTypeKey(constype), this.toTIRTypeKey(ResolvedType.createSingle(ccdecl.representation)));
            return this.setResultExpression(env, nexp, constype, constype, undefined);
        }
    }

    private checkAccessFormatInfo(env: ExpressionTypeEnvironment, exp: AccessFormatInfo): ExpressionTypeEnvironment {
        assert(false, "TODO: maybe this is ok for string formats but right now this shouldn't happen");

        return env;
    }

    private checkAccessEnvValue(env: ExpressionTypeEnvironment, exp: AccessEnvValue): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_isTaskFile, `Can only access "environment" variables in task actions`);

        const valtype = this.normalizeTypeOnly(exp.valtype, env.binds);
        const restype = this.normalizeTypeOnly(new UnionTypeSignature(exp.sinfo, [exp.valtype, new NominalTypeSignature(exp.sinfo, "Core", ["None"])]), env.binds);

        return this.setResultExpression(env, new TIRAccessEnvValue(exp.sinfo, exp.keyname, this.toTIRTypeKey(valtype), this.toTIRTypeKey(restype), exp.orNoneMode), restype, restype, undefined);
    }

    private checkAccessNamespaceConstant(env: ExpressionTypeEnvironment, exp: AccessNamespaceConstantExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        this.raiseErrorIf(exp.sinfo, !nsdecl.consts.has(exp.name), `Constant named '${exp.name}' is not defined`);
        const cdecl = nsdecl.consts.get(exp.name) as NamespaceConstDecl;

        this.raiseErrorIf(exp.sinfo, cdecl.value.captured.size !== 0, "Expression uses unbound variables");
        const cexp = this.compileTimeReduceConstantExpression(cdecl.value.exp, TemplateBindScope.createEmptyBindScope());
        const rtype = this.normalizeTypeOnly(cdecl.declaredType, TemplateBindScope.createEmptyBindScope());

        if (cexp !== undefined) {
            return this.checkExpression(env, cexp, undefined);
        }
        else {
            const nskey = TIRMemberIDGenerator.generateNamespaceConstID(exp.ns, exp.name);
            const nname = new TIRNamespaceMemberName(exp.ns, exp.name);
            const tirrtype = this.toTIRTypeKey(rtype);

            this.m_pendingNamespaceConsts.push(cdecl);
            return this.setResultExpression(env, new TIRAccessNamespaceConstantExpression(exp.sinfo, nskey, nname, tirrtype), rtype, rtype, undefined);
        }
    }

    private checkAccessStaticField(env: ExpressionTypeEnvironment, exp: AccessStaticFieldExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.stype, env.binds);
        const cmf = this.resolveMemberConst(exp.sinfo, oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, cmf === undefined, `const ${exp.name} not defined on type ${oftype.typeID}`);

        const cdecl = (cmf as OOMemberLookupInfo<StaticMemberDecl>);
        this.raiseErrorIf(exp.sinfo, (cdecl.decl.value as ConstantExpressionValue).captured.size !== 0, "Expression uses unbound variables");
        const cexp = this.compileTimeReduceConstantExpression((cdecl.decl.value as ConstantExpressionValue).exp, env.binds);
        const rtype = this.normalizeTypeOnly(cdecl.decl.declaredType, TemplateBindScope.createBaseBindScope(cdecl.oobinds));
        
        if (cexp !== undefined) {
            return this.checkExpression(env, cexp, undefined);
        }
        else {
            const sfkey = TIRMemberIDGenerator.generateMemberConstID(cdecl.ttype.typeID, exp.name);
            const etname = new TIRTypeName(cdecl.ootype.ns, cdecl.ootype.name, cdecl.ootype.terms.map((tt) => this.toTIRTypeKey(cdecl.oobinds.get(tt.name) as ResolvedType)));
            const sfname = new TIRTypeMemberName(etname, exp.name, undefined);
            const tirrtype = this.toTIRTypeKey(rtype);

            this.m_pendingConstMemberDecls.push(cdecl);
            return this.setResultExpression(env, new TIRAccessConstMemberFieldExpression(exp.sinfo, sfkey, sfname, tirrtype), rtype, rtype, undefined);
        }
    }

    private checkAccessVariable(env: ExpressionTypeEnvironment, exp: AccessVariableExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);

        const vinfo = env.lookupVar(exp.name) as VarInfo;
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not have been assigned a value");

        return this.setResultExpression(env, new TIRAccessVariableExpression(exp.sinfo, exp.name, this.toTIRTypeKey(vinfo.declaredType)), vinfo.declaredType, vinfo.flowType, undefined);
    }

    private checkConstructorPrimary(env: ExpressionTypeEnvironment, exp: ConstructorPrimaryExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.ctype, env.binds).tryGetUniqueEntityTypeInfo();
        this.raiseErrorIf(exp.sinfo, oftype === undefined, "Invalid constructor type");

        if(oftype instanceof ResolvedObjectEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);
            const tirobj = this.m_tirTypeMap.get(tiroftype) as TIRObjectEntityType;

            const allf = [...this.getAllOOFields(roftype, oftype.object, oftype.binds)];
            this.raiseErrorIf(exp.sinfo, allf.length !== exp.args.length, `got ${exp.args.length} args for constructor but expected ${allf.length}`);
            const eargs = exp.args.map((arg, i) => {
                const itype = this.normalizeTypeOnly(allf[i][1][2].declaredType, TemplateBindScope.createBaseBindScope(allf[i][1][3]));
                const ee = this.checkExpression(env, arg, itype, undefined);

                return this.emitCoerceIfNeeded(ee, exp.sinfo, itype);
            });

            if(!this.entityTypeConstructorHasInvariants(roftype, oftype.object, oftype.binds)) {
                const econs = new TIRConstructorPrimaryDirectExpression(exp.sinfo, tiroftype, eargs.map((earg) => earg.expressionResult));
                return this.setResultExpression(env, econs, roftype, roftype, undefined);
            }
            else {
                const econs = new TIRConstructorPrimaryCheckExpression(exp.sinfo, tiroftype, eargs.map((earg) => earg.expressionResult));
                return this.setResultExpression(env, econs, roftype, roftype, undefined);
            }
        }
        else if(oftype instanceof ResolvedTypedeclEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);

            this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, `${oftype.typeID} constructor expects a single arg`);
            const cexp = this.checkExpression(env, exp.args[0], ResolvedType.createSingle(oftype.valuetype), undefined);
            const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, ResolvedType.createSingle(oftype.valuetype));

            if (!this.typedeclTypeConstructorFromValueHasInvariants(roftype, oftype.object)) {
                const nexp = new TIRTypedeclDirectExpression(exp.sinfo, this.toTIRTypeKey(roftype), ecast.expressionResult);
                return this.setResultExpression(env, nexp, roftype, roftype, undefined);
            }
            else {
                const nexp = new TIRTypedeclConstructorExpression(exp.sinfo, this.toTIRTypeKey(roftype), ecast.expressionResult);
                return this.setResultExpression(env, nexp, roftype, roftype, undefined);
            }
        }
        else if(oftype instanceof ResolvedConstructableEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            if(oftype instanceof ResolvedOkEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Result<T, E>::Ok constructor expects a single arg of type T");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeT, undefined);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeT);

                return this.setResultExpression(env, new TIRSpecialConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype, roftype, undefined);
            }
            else if(oftype instanceof ResolvedErrEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Result<T, E>::Ok constructor expects a single arg of type E");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeE, undefined);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeE);

                return this.setResultExpression(env, new TIRSpecialConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype, roftype, undefined);
            }
            else if(oftype instanceof ResolvedSomethingEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Something<T> constructor expects a single arg of type T");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeT, undefined);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeT);

                return this.setResultExpression(env, new TIRSpecialConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype, roftype, undefined);
            }
            else if(oftype instanceof ResolvedMapEntityAtomType) {
                const tirktype = this.toTIRTypeKey(oftype.typeK);
                const tirvtype = this.toTIRTypeKey(oftype.typeV);

                this.raiseErrorIf(exp.sinfo, exp.args.length !== 2, "MapEntry<K, V> constructor expects two args of type K, V");
                const kexp = this.checkExpression(env, exp.args[0], oftype.typeK, undefined);
                const vexp = this.checkExpression(env, exp.args[1], oftype.typeV, undefined);

                const kcast = this.emitCoerceIfNeeded(kexp, exp.args[0].sinfo, oftype.typeK);
                const vcast = this.emitCoerceIfNeeded(vexp, exp.args[1].sinfo, oftype.typeV);

                return this.setResultExpression(env, new TIRMapEntryConstructorExpression(exp.sinfo, kcast.expressionResult, vcast.expressionResult, tirktype, tirvtype, tiroftype), ResolvedType.createSingle(oftype), ResolvedType.createSingle(oftype), undefined);
            }
            else {
                this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${oftype.typeID}`);
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype, roftype, undefined);
            }
        }
        else if (oftype instanceof ResolvedPrimitiveCollectionEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            if(oftype instanceof ResolvedListEntityAtomType) {
                const eargs = exp.args.map((arg) => {
                    const texp = this.checkExpression(env, arg, oftype.typeT, undefined);
                    return this.emitCoerceIfNeeded(texp, exp.sinfo, oftype.typeT);
                });

                return this.setResultExpression(env, new TIRConstructorListExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype, roftype, undefined);
            }
            else if(oftype instanceof ResolvedStackEntityAtomType) {
                this.raiseError(exp.sinfo, "Stack<T> not fully supported yet");
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype, roftype, undefined);
            }
            else if(oftype instanceof ResolvedQueueEntityAtomType) {
                this.raiseError(exp.sinfo, "Queue<T> not fully supported yet");
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype, roftype, undefined);
            }
            else if(oftype instanceof ResolvedSetEntityAtomType) {
                this.raiseError(exp.sinfo, "Set<T> not fully supported yet");
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype, roftype, undefined);
            }
            else if(oftype instanceof ResolvedMapEntityAtomType) {
                const metype = this.normalizeTypeOnly(new NominalTypeSignature(exp.sinfo, "Core", ["MapEntry"], [new TemplateTypeSignature(exp.sinfo, "K"), new TemplateTypeSignature(exp.sinfo, "V")]), TemplateBindScope.createDoubleBindScope("K", oftype.typeK, "V", oftype.typeV));
                
                const eargs = exp.args.map((arg) => {
                    const texp = this.checkExpression(env, arg, metype, undefined);
                    return this.emitCoerceIfNeeded(texp, exp.sinfo, metype);
                });

                return this.setResultExpression(env, new TIRConstructorMapExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype, roftype, undefined);
            }
            else {
                this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${oftype.typeID}`);
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype, roftype, undefined);
            }
        }
        else {
            this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${exp.ctype.getDiagnosticName()}`);
            return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, "None"), ResolvedType.createInvalid(), ResolvedType.createInvalid(), undefined);
        }
    }

    private checkTupleConstructor(env: ExpressionTypeEnvironment, exp: ConstructorTupleExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedTupleAtomType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedTupleAtomType && desiredtype.options[0].types.length === exp.args.length) {
            itype = desiredtype.options[0]
        }

        if(itype === undefined) {
            const eargs = exp.args.map((arg) => this.checkExpression(env, arg, undefined, undefined));

            const roftype = ResolvedType.createSingle(ResolvedTupleAtomType.create(eargs.map((ee) => ee.tinfer)));
            const tiroftype = this.toTIRTypeKey(roftype);

            const cargs = eargs.map((arg) => this.emitCoerceIfNeeded(arg, exp.sinfo, arg.tinfer));
            return this.setResultExpression(env, new TIRConstructorTupleExpression(exp.sinfo, tiroftype, cargs.map((arg) => arg.expressionResult)), roftype, roftype, undefined);
        }
        else {
            const topts = itype.types;
            const eargs = exp.args.map((arg, i) => {
                const texp = this.checkExpression(env, arg, topts[i], undefined);
                return this.emitCoerceIfNeeded(texp, exp.sinfo, topts[i]);
            });
        
            const roftype = ResolvedType.createSingle(itype);
            const tiroftype = this.toTIRTypeKey(roftype);

            return this.setResultExpression(env, new TIRConstructorTupleExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype, roftype, undefined);
        }
    }

    private checkRecordConstructor(env: ExpressionTypeEnvironment, exp: ConstructorRecordExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedRecordAtomType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedRecordAtomType && desiredtype.options[0].entries.length === exp.args.length) {
            itype = desiredtype.options[0]
        }

        if(itype === undefined) {
            const eargs = exp.args.map((arg) => {
                const cc = this.checkExpression(env, arg.value, undefined, undefined);
                return {pname: arg.property, penv: cc};
            });

            const roftype = ResolvedType.createSingle(ResolvedRecordAtomType.create(eargs.map((ee) => {
                return {pname: ee.pname, ptype: ee.penv.tinfer};
            })));
            const tiroftype = this.toTIRTypeKey(roftype);

            const cargs = eargs.map((arg) => this.emitCoerceIfNeeded(arg.penv, exp.sinfo, arg.penv.tinfer));
            return this.setResultExpression(env, new TIRConstructorRecordExpression(exp.sinfo, tiroftype, cargs.map((arg) => arg.expressionResult)), roftype, roftype, undefined);
        }
        else {
            const roftype = ResolvedType.createSingle(itype);
            const tiroftype = this.toTIRTypeKey(roftype);

            for(let i = 0; i < itype.entries.length; ++i) {
                if(itype.entries[i].pname !== exp.args[i].property) {
                    this.raiseError(exp.sinfo, `expected property name ${itype.entries[i].pname} but got ${exp.args[i].property}`);
                    return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, "None"), roftype, roftype, undefined);
                }
            }

            const topts = itype.entries;
            const eargs = exp.args.map((arg, i) => {
                const texp = this.checkExpression(env, arg.value, topts[i].ptype, undefined);
                return this.emitCoerceIfNeeded(texp, exp.sinfo, topts[i].ptype);
            });

            return this.setResultExpression(env, new TIRConstructorTupleExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype, roftype, undefined);
        }
    }

    private checkConstructorEphemeralValueList(env: ExpressionTypeEnvironment, exp: ConstructorEphemeralValueList, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedEphemeralListType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedEphemeralListType && desiredtype.options[0].types.length === exp.args.length) {
            itype = desiredtype.options[0]
        }

        if(itype === undefined) {
            const eargs = exp.args.map((arg) => this.checkExpression(env, arg, undefined, undefined));

            const roftype = ResolvedType.createSingle(ResolvedEphemeralListType.create(eargs.map((ee) => ee.tinfer)));
            const tiroftype = this.toTIRTypeKey(roftype);

            const cargs = eargs.map((arg) => this.emitCoerceIfNeeded(arg, exp.sinfo, arg.tinfer));
            return this.setResultExpression(env, new TIRConstructorEphemeralValueList(exp.sinfo, tiroftype, cargs.map((arg) => arg.expressionResult)), roftype, roftype, undefined);
        }
        else {
            const topts = itype.types;
            const eargs = exp.args.map((arg, i) => {
                const texp = this.checkExpression(env, arg, topts[i], undefined);
                return this.emitCoerceIfNeeded(texp, exp.sinfo, topts[i]);
            });
        
            const roftype = ResolvedType.createSingle(itype);
            const tiroftype = this.toTIRTypeKey(roftype);

            return this.setResultExpression(env, new TIRConstructorEphemeralValueList(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype, roftype, undefined);
        }
    }

    private checkSpecialConstructorExpression(env: ExpressionTypeEnvironment, exp: SpecialConstructorExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        if(exp.rop === "something") {
            this.raiseErrorIf(exp.sinfo, desiredtype !== undefined && (desiredtype.options.length !== 1 || !(desiredtype.typeID.startsWith("Option<"))), "something shorthand constructors only valid with Option typed expressions");
            const T = desiredtype !== undefined && desiredtype.options.length === 1 ? (desiredtype.options[0] as ResolvedConceptAtomType).getTBind() : undefined;

            const cexp = this.checkExpression(env, exp.arg, T, undefined);
            const ecast = T !== undefined ? this.emitCoerceIfNeeded(cexp, exp.sinfo, T) : cexp;

            const roftype = this.getSomethingType(T || cexp.tinfer);
            const tiroftype = this.toTIRTypeKey(roftype);

            const consenv = this.setResultExpression(ecast, new TIRSpecialConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype, roftype, undefined);
            if(desiredtype === undefined) {
                return consenv; 
            }
            else {
                return this.emitCoerceIfNeeded(consenv, exp.sinfo, desiredtype);
            }
        }
        else {
            this.raiseErrorIf(exp.sinfo, desiredtype === undefined || (desiredtype.options.length !== 1 || !(desiredtype as ResolvedType).typeID.startsWith("Result<")), "ok/err shorthand constructors only valid with Result typed expressions");
            const T = ((desiredtype as ResolvedType).options[0] as ResolvedConceptAtomType).getTBind();
            const E = ((desiredtype as ResolvedType).options[0] as ResolvedConceptAtomType).getEBind();

            if (exp.rop === "ok") {
                const okenv = this.checkExpression(env, exp.arg, T, undefined);
                const tcast = this.emitCoerceIfNeeded(okenv, exp.sinfo, T);

                const rokconstype = this.getOkType(T, E);
                const tirokconstype = this.toTIRTypeKey(rokconstype);

                const consenv = this.setResultExpression(tcast, new TIRSpecialConstructorExpression(exp.sinfo, tirokconstype, tcast.expressionResult), rokconstype, rokconstype, undefined);
                return this.emitCoerceIfNeeded(consenv, exp.sinfo, desiredtype as ResolvedType);
            }
            else {
                const okenv = this.checkExpression(env, exp.arg, E, undefined);
                const tcast = this.emitCoerceIfNeeded(okenv, exp.sinfo, E);

                const rerrconstype = this.getOkType(T, E);
                const tirerrconstype = this.toTIRTypeKey(rerrconstype);

                const consenv = this.setResultExpression(tcast, new TIRSpecialConstructorExpression(exp.sinfo, tirerrconstype, tcast.expressionResult), rerrconstype, rerrconstype, undefined);
                return this.emitCoerceIfNeeded(consenv, exp.sinfo, desiredtype as ResolvedType);
            }
        }
    }

    private checkPCodeInvokeExpression(env: ExpressionTypeEnvironment, exp: PCodeInvokeExpression): ExpressionTypeEnvironment[] {
        const pco = env.lookupPCode(exp.pcode);
        this.raiseErrorIf(exp.sinfo, pco === undefined, "Code name not defined");
        const pcode = pco as PCode;
        const captured = [...(pco as PCode).captured].map((cc) => cc[0]).sort();

        const callargs = [...exp.args.argList];
        const eargs = this.checkArgumentsEvaluationWSig(exp.sinfo, env, pcode.ftype, new Map<string, ResolvedType>(), new Arguments(callargs), undefined, refok);

        const margs = this.checkArgumentsSignature(exp.sinfo, env, "pcode", pcode.ftype, eargs);
        const cargsext = captured.map((carg) => new MIRRegisterArgument(this.m_emitter.generateCapturedVarName(carg, pcode.code.bodyID)));
        const iargsext = this.m_emitter.flattenCapturedPCodeVarCaptures(pcode.capturedpcode).map((iarg) => new MIRRegisterArgument(iarg));
 
        this.checkRecursion(exp.sinfo, pcode.ftype, margs.pcodes, exp.rec);

        const refinfo = this.generateRefInfoForCallEmit((pcode as PCode).ftype, margs.refs);
        this.m_emitter.emitInvokeFixedFunction(exp.sinfo, (pcode as PCode).ikey, [...margs.args, ...cargsext, ...iargsext], undefined, refinfo, trgt);   

        return this.updateEnvForOutParams(env.setUniformResultExpression(pcode.ftype.resultType), margs.refs);
    }

    private checkCallNamespaceFunctionOrOperatorExpression(env: ExpressionTypeEnvironment, exp: CallNamespaceFunctionOrOperatorExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        if(nsdecl.ns === "Core" && exp.name === "s_safeAs") {
            const argenv = this.checkExpression(env, exp.args[0], this.normalizeTypeOnly(exp.terms[0], env.binds), undefined);
            const astype = this.normalizeTypeOnly(exp.terms[1], env.binds);

            return this.emitSafeCoerceIfNeeded(argenv, exp.sinfo, astype);
        }
        else {
            if (nsdecl.operators.has(exp.name)) {
                const opsintro = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).find((nso) => nso.doesKindTagMatch(exp.opkind) && OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));
                const opdecls = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).filter((nso) => nso.doesKindTagMatch(exp.opkind) && !OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));
                this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

                const pnames = (opsintro as NamespaceOperatorDecl).invoke.params.map((p) => p.name);
                const hasrest = (opsintro as NamespaceOperatorDecl).invoke.optRestType !== undefined;

                //No terms to be bound on operator call

                const eargs = this.checkArgumentsEvaluationWOperator(exp.sinfo, env, env.terms, exp.args, refok);
                const rargs = this.checkArgumentsWOperator(exp.sinfo, env, pnames, hasrest, eargs);

                const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
                const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types.map((vt) => vt.flowtype), isigs);

                this.raiseErrorIf(exp.sinfo, opidx === -1 || (opsintro !== undefined && opsintro.isDynamic), `Cannot resolve operator: ${exp.name}`);
                const opdecl = opidx !== -1 ? opdecls[opidx] : opsintro as NamespaceOperatorDecl;

                return this.checkNamespaceOperatorInvoke(exp.sinfo, env, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, exp.rec, trgt, refok);
            }
            else {
                this.raiseErrorIf(exp.sinfo, !nsdecl.functions.has(exp.name), `Function named '${exp.name}' is not defined`);
                const fdecl = nsdecl.functions.get(exp.name) as NamespaceFunctionDecl;

                this.raiseErrorIf(exp.sinfo, fdecl.invoke.terms.length !== exp.terms.length, "missing template types");
                let binds = new Map<string, ResolvedType>();
                for(let i = 0; i < fdecl.invoke.terms.length; ++i) {
                    binds.set(fdecl.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], TemplateBindScope.createEmptyBindScope()));
                }
                this.checkTemplateTypesOnInvoke(exp.sinfo, fdecl.invoke.terms, TemplateBindScope.createEmptyBindScope(), binds, fdecl.invoke.termRestrictions);

                const fkey = TIRInvokeIDGenerator.generateInvokeIDForNamespaceFunction(nsdecl.ns, exp.name, fdecl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
                const rtype = this.normalizeTypeOnly(fdecl.invoke.resultType, TemplateBindScope.createBaseBindScope(binds));
                const tirrtype = this.toTIRTypeKey(rtype);

                const argexps = this.checkArgumentList(exp.sinfo, env, exp.args, fdecl.invoke.params.map((pp) => pp.type), TemplateBindScope.createBaseBindScope(binds));

                if(this.hasPreconditions(fdecl.invoke) || this.hasPostconditions(fdecl.invoke)) {
                    const tircall = new TIRCallNamespaceFunctionExpression(exp.sinfo, fkey, tirrtype, argexps);
                    return this.setResultExpression(env, tircall, rtype, rtype, undefined);
                }
                else {
                    const tircall = new TIRCallNamespaceFunctionWithChecksExpression(exp.sinfo, fkey, tirrtype, argexps);
                    return this.setResultExpression(env, tircall, rtype, rtype, undefined);
                }
            }
        }
    }

    private checkCallStaticFunctionExpression(env: ExpressionTypeEnvironment, exp: CallStaticFunctionExpression): ExpressionTypeEnvironment[] {
        const fromtype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ttype, env.terms);
        const fdecltry = this.m_assembly.tryGetFunctionUniqueDeclFromType(fromtype, exp.name);
        const opdecltry = this.m_assembly.tryGetOperatorUniqueDeclFromType(fromtype, exp.name);

        this.raiseErrorIf(exp.sinfo, (fdecltry === undefined && opdecltry === undefined), `Static function/operator not defined for type ${fromtype.typeID}`);
        this.raiseErrorIf(exp.sinfo, (fdecltry !== undefined && opdecltry !== undefined), `Static function/operator multiply defined for type ${fromtype.typeID}`);

        if(fromtype.typeID === "KeyType" && (exp.name === "less" || exp.name === "equal")) {
            const ktype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.terms.targs[0], env.terms);
            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(ktype, this.m_assembly.getSpecialKeyTypeConceptType()) || !ktype.isGroundedType(), "Invalid argument");

            const lhsexp = exp.args.argList[0].value;
            const lhsreg = this.m_emitter.generateTmpRegister();
            const tlhs = this.checkExpression(env, lhsexp, lhsreg, undefined).getExpressionResult().valtype;

            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(tlhs.flowtype, ktype), "Invalid argument");
            this.raiseErrorIf(exp.sinfo, !tlhs.flowtype.isGroundedType(), "Invalid argument");

            const rhsexp = exp.args.argList[1].value;
            const rhsreg = this.m_emitter.generateTmpRegister();
            const trhs = this.checkExpression(env, rhsexp, rhsreg, undefined).getExpressionResult().valtype;

            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(trhs.flowtype, ktype), "Invalid argument");
            this.raiseErrorIf(exp.sinfo, !trhs.flowtype.isGroundedType(), "Invalid argument");

            if (exp.name === "equal") {
                this.m_emitter.emitBinKeyEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(tlhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(trhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(ktype), trgt, undefined, this.m_emitter.registerResolvedTypeReference(tlhs.flowtype), this.m_emitter.registerResolvedTypeReference(trhs.flowtype));
            }
            else {
                this.m_emitter.emitBinKeyLess(exp.sinfo, this.m_emitter.registerResolvedTypeReference(tlhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(trhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(ktype), trgt, this.m_emitter.registerResolvedTypeReference(tlhs.flowtype), this.m_emitter.registerResolvedTypeReference(trhs.flowtype));
            }

            return [env.setUniformResultExpression(this.m_assembly.getSpecialBoolType())];
        }
        else {
            if (opdecltry !== undefined) {
                const oodecl = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).contiainingType;
                const oobinds = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).binds;

                const opsintro = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).decl.find((nso) => nso.doesKindTagMatch(exp.opkind) && OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));
                const opdecls = (opdecltry as OOMemberLookupInfo<StaticOperatorDecl[]>).decl.filter((nso) => nso.doesKindTagMatch(exp.opkind) && !OOPTypeDecl.attributeSetContains("abstract", nso.invoke.attributes));
                this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one decl");

                const pnames = (opsintro as StaticOperatorDecl).invoke.params.map((p) => p.name);
                const hasrest = (opsintro as StaticOperatorDecl).invoke.optRestType !== undefined;

                //No terms to be bound on operator call

                const eargs = this.checkArgumentsEvaluationWOperator(exp.sinfo, env, env.terms, exp.args, refok);
                const rargs = this.checkArgumentsWOperator(exp.sinfo, env, pnames, hasrest, eargs);

                const isigs = opdecls.map((opd) => this.m_assembly.normalizeTypeFunction(opd.invoke.generateSig(), new Map<string, ResolvedType>()) as ResolvedFunctionType);
                const opidx = this.m_assembly.tryGetUniqueStaticOperatorResolve(rargs.types.map((vt) => vt.flowtype), isigs);

                this.raiseErrorIf(exp.sinfo, opidx !== -1 || (opsintro !== undefined && opsintro.isDynamic), `Cannot resolve operator: ${exp.name}`);
                const opdecl = opidx !== -1 ? opdecls[opidx] : opsintro as StaticOperatorDecl;
            
                return this.checkStaticOperatorInvoke(exp.sinfo, env, oodecl, oobinds, opdecl, rargs.args, rargs.types, rargs.refs, rargs.pcodes, rargs.cinfo, exp.rec, trgt, refok); 
            }
            else {
                const fdecl = fdecltry as OOMemberLookupInfo<StaticFunctionDecl>;

                const [fsig, callbinds, eargs] = this.inferAndCheckArguments(exp.sinfo, env, exp.args, fdecl.decl.invoke, exp.terms.targs, fdecl.binds, env.terms, undefined, refok);
                this.checkTemplateTypes(exp.sinfo, fdecl.decl.invoke.terms, callbinds, fdecl.decl.invoke.termRestrictions);

                const rargs = this.checkArgumentsSignature(exp.sinfo, env, exp.name, fsig, eargs);
                this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.rec);


                if (fdecl.decl.invoke.body !== undefined && fdecl.decl.invoke.body.body === "special_inject") {
                    this.m_emitter.emitInject(exp.sinfo, this.m_emitter.registerResolvedTypeReference(fsig.params[0].type as ResolvedType), this.m_emitter.registerResolvedTypeReference(fsig.resultType), rargs.args[0], trgt);

                    return [env.setUniformResultExpression(fsig.resultType)];
                }
                else if (fdecl.decl.invoke.body !== undefined && fdecl.decl.invoke.body.body === "special_extract") {
                    this.m_emitter.emitExtract(exp.sinfo, this.m_emitter.registerResolvedTypeReference(fsig.params[0].type as ResolvedType), this.m_emitter.registerResolvedTypeReference(fsig.resultType), rargs.args[0], trgt);

                    return [env.setUniformResultExpression(fsig.resultType)];
                }
                else {
                    const ootype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(fdecl.contiainingType, fdecl.binds));
                    const ckey = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(fdecl.contiainingType, fdecl.binds), [ootype, fdecl.contiainingType, fdecl.binds], fdecl.decl, exp.name, callbinds, rargs.pcodes, rargs.cinfo);
                    const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                    this.m_emitter.emitInvokeFixedFunction(exp.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);

                    return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
                }
            }
        }
    }

    private checkLogicActionExpression(env: ExpressionTypeEnvironment, exp: LogicActionExpression): ExpressionTypeEnvironment {
        let bargs = this.checkArgumentsEvaluationLogicAction(env, exp.args);
        this.m_emitter.emitLogicAction(exp.sinfo, trgt, exp.opkind, bargs);
        
        return env.setUniformResultExpression(this.m_assembly.getSpecialBoolType());
    }

    private checkIsTypeExpression_commondirect(sinfo: SourceInfo, env: ExpressionTypeEnvironment, arg: MIRRegisterArgument, oftype: ResolvedType): ExpressionTypeEnvironment[] {
        const tsplits = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);
        this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(oftype), arg, this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.flowtype), undefined);
        return [
            ...(tsplits.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))), 
            ...(tsplits.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
        ];
    } 

    private checkIsTypeExpression_common(sinfo: SourceInfo, env: ExpressionTypeEnvironment, arg: Expression, oftype: ResolvedType, trgt: MIRRegisterArgument, refok: boolean): ExpressionTypeEnvironment[] {
        const treg = this.m_emitter.generateTmpRegister();
        const fenv = this.checkExpression(env, arg, treg, oftype, { refok: refok, orok: false });

        return this.checkIsTypeExpression_commondirect(sinfo, fenv, treg, oftype, trgt);
    } 

    private checkIsTypeExpressionMulti(env: ExpressionTypeEnvironment, exp: IsTypeExpression, trgt: MIRRegisterArgument, refok: boolean): ExpressionTypeEnvironment[] {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.oftype, env.terms);
        return this.checkIsTypeExpression_common(exp.sinfo, env, exp.arg, oftype, trgt, refok);
    }

    private checkAsTypeExpression_commondirect(sinfo: SourceInfo, env: ExpressionTypeEnvironment, arg: MIRRegisterArgument, oftype: ResolvedType): ExpressionTypeEnvironment[] {
        const tsplits = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);

        if (tsplits.tenvs.length === 0) {
            this.m_emitter.emitAbort(sinfo, "Never of required type");

            //
            //TODO: we would like to set the flow as infeasible -- but exps don't like that so do abort w/ dummy assign for now 
            //[env.setAbort()]
            //

            this.m_emitter.emitLoadUninitVariableValue(sinfo, this.m_emitter.registerResolvedTypeReference(oftype), trgt);
            return [env.setUniformResultExpression(oftype)];
        }
        else {
            if (tsplits.fenvs.length !== 0) {
                const creg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, creg, this.m_emitter.registerResolvedTypeReference(oftype), arg, this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(env.getExpressionResult().valtype.flowtype), undefined);
                this.m_emitter.emitAssertCheck(sinfo, "Failed type conversion", creg);
            }

            this.m_emitter.emitRegisterStore(sinfo, arg, this.emitInlineConvertIfNeeded(sinfo, trgt, env.getExpressionResult().valtype, oftype), this.m_emitter.registerResolvedTypeReference(oftype), undefined);
            return tsplits.tenvs;
        }
    }

    private checkAsTypeExpression_common(sinfo: SourceInfo, env: ExpressionTypeEnvironment, arg: Expression, oftype: ResolvedType, trgt: MIRRegisterArgument, refok: boolean): ExpressionTypeEnvironment[] {
        const treg = this.m_emitter.generateTmpRegister();
        const fenv = this.checkExpression(env, arg, treg, oftype, { refok: refok, orok: false });

        return this.checkAsTypeExpression_commondirect(sinfo, fenv, treg, oftype, trgt);
    } 

    private checkAsTypeExpressionMulti(env: ExpressionTypeEnvironment, exp: AsTypeExpression, trgt: MIRRegisterArgument, refok: boolean): ExpressionTypeEnvironment[] {
        const oftype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.oftype, env.terms);
        return this.checkAsTypeExpression_common(exp.sinfo, env, exp.arg, oftype, trgt, refok);
    }

    private checkAccessFromIndex(env: ExpressionTypeEnvironment, op: PostfixAccessFromIndex, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        const texp = env.getExpressionResult().valtype;

        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");
        this.raiseErrorIf(op.sinfo, this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.index) !== "yes", "Index may not be defined for tuple");

        const idxtype = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.index);
        this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.index, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(idxtype), trgt);

        return env.setUniformResultExpression(idxtype);
    }

    private checkAccessFromName(env: ExpressionTypeEnvironment, op: PostfixAccessFromName, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        const texp = env.getExpressionResult().valtype;

        if (texp.flowtype.isRecordTargetType()) {
            this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Base of property access expression must be of Record type");
            this.raiseErrorIf(op.sinfo, this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.name) !== "yes", `Property "${op.name}" may not be defined for record`);

            const rtype = this.getInfoForLoadFromSafeProperty(op.sinfo, texp.flowtype, op.name);
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.name, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(rtype), trgt);

            return env.setUniformResultExpression(rtype);
        }
        else {
            const tryfinfo = this.m_assembly.tryGetFieldUniqueDeclFromType(texp.flowtype, op.name);
            this.raiseErrorIf(op.sinfo, tryfinfo === undefined, `Field name "${op.name}" is not defined (or is multiply) defined`);

            const finfo = tryfinfo as OOMemberLookupInfo<MemberFieldDecl>;
            const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, finfo.decl.declaredType, finfo.binds);
            
            const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(finfo.contiainingType, finfo.binds), op.name);
            this.m_emitter.emitLoadField(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), fkey, !texp.flowtype.isUniqueCallTargetType(), this.m_emitter.registerResolvedTypeReference(ftype), trgt);
            
            return env.setUniformResultExpression(ftype);
        }
    }

    private checkPostfixIsMulti(env: ExpressionTypeEnvironment, op: PostfixIs, arg: MIRRegisterArgument): ExpressionTypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        const oftype = this.resolveAndEnsureTypeOnly(op.sinfo, op.istype, env.terms);

        this.m_emitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(oftype), arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), undefined);
        
        const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, oftype, [env]);
        return [
            ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))), 
            ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
        ];
    }

    private checkPostfixIsMono(env: ExpressionTypeEnvironment, op: PostfixIs, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        return ExpressionTypeEnvironment.join(this.m_assembly, ...this.checkPostfixIsMulti(env, op, arg, trgt));
    }

    private checkPostfixAs(env: ExpressionTypeEnvironment, op: PostfixAs, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        const astype = this.resolveAndEnsureTypeOnly(op.sinfo, op.astype, env.terms);

        const tsplits = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, astype, [env]);
        assert(tsplits.tenvs.length <= 1);

        if (tsplits.tenvs.length === 0) {
            this.m_emitter.emitAbort(op.sinfo, "Never of required type");

                        //
            //TODO: we would like to set the flow as infeasible -- but exps don't like that so do abort w/ dummy assign for now 
            //[env.setAbort()]
            //

            this.m_emitter.emitLoadUninitVariableValue(op.sinfo, this.m_emitter.registerResolvedTypeReference(astype), trgt);
            return env.setUniformResultExpression(astype);
        }
        else {
            if (tsplits.fenvs.length !== 0) {
                const creg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(op.sinfo, creg, this.m_emitter.registerResolvedTypeReference(astype), arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), undefined);
                this.m_emitter.emitAssertCheck(op.sinfo, "Failed type conversion", creg);
            }

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, arg, new ValueType(texp.layout, astype), astype), trgt, this.m_emitter.registerResolvedTypeReference(astype), undefined);
            return tsplits.tenvs[0].setResultExpression(astype, astype, undefined, undefined);
        }
    }

    private checkPostfixHasIndexMulti(env: ExpressionTypeEnvironment, op: PostfixHasIndex, arg: MIRRegisterArgument): ExpressionTypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Can only check for indecies on tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.idx);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, trgt);
            return [env.setUniformResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            this.m_emitter.emitLoadConstBool(op.sinfo, true, trgt);
            return [env.setUniformResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else {
            assert(!texp.flowtype.isUniqueTupleTargetType(), "If this is unique then we should have been in one of the cases above");

            this.m_emitter.emitTupleHasIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, trgt);
            
            const renvs = ExpressionTypeEnvironment.convertToHasIndexNotHasIndexFlowsOnResult(this.m_assembly, op.idx, [env]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
    }

    private checkPostfixHasIndexMono(env: ExpressionTypeEnvironment, op: PostfixHasIndex, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        return ExpressionTypeEnvironment.join(this.m_assembly, ...this.checkPostfixHasIndexMulti(env, op, arg, trgt));
    }

    private checkPostfixGetIndexOrNone(env: ExpressionTypeEnvironment, op: PostfixGetIndexOrNone, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.idx);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstNone(op.sinfo, trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialNoneType());
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.idx);

            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), trgt);
            return env.setUniformResultExpression(linfo);
        }
        else {
            const ttype = this.getInfoForLoadFromSafeIndexOnly(op.sinfo, texp.flowtype, op.idx);
            const linfo = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), ttype]);

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNone(), ValueType.createUniform(this.m_assembly.getSpecialNoneType()), linfo), trgt, this.m_emitter.registerResolvedTypeReference(linfo), undefined);

            const loadreg = this.m_emitter.generateTmpRegister();
            const hasreg = this.m_emitter.generateTmpRegister();
            const guard = new MIRArgGuard(hasreg);
            this.m_emitter.emitLoadTupleIndexSetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(ttype), loadreg, guard);
            if(ttype.isSameType(linfo)) {
                this.m_emitter.emitRegisterStore(op.sinfo, loadreg, trgt, this.m_emitter.registerResolvedTypeReference(linfo), new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            }
            else {
                this.m_emitter.emitConvert(op.sinfo, this.m_emitter.registerResolvedTypeReference(ttype), this.m_emitter.registerResolvedTypeReference(ttype), this.m_emitter.registerResolvedTypeReference(linfo), loadreg, trgt, new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            }

            return env.setUniformResultExpression(linfo);
        }
    }

    private checkPostfixGetIndexOption(env: ExpressionTypeEnvironment, op: PostfixGetIndexOption, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.idx);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstNothing(op.sinfo, trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialNothingType());
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.idx);
            const somethingtype = this.m_assembly.getSomethingType(linfo);
            const mirsomethingtype = this.m_emitter.registerResolvedTypeReference(somethingtype);

            const loadreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), loadreg);
            this.m_emitter.emitInject(op.sinfo, this.m_emitter.registerResolvedTypeReference(linfo), mirsomethingtype, loadreg, trgt);

            return env.setUniformResultExpression(somethingtype);
        }
        else {
            const linfo = this.getInfoForLoadFromSafeIndexOnly(op.sinfo, texp.flowtype, op.idx);
            const somethingtype = this.m_assembly.getSomethingType(linfo);
            const mirsomethingtype = this.m_emitter.registerResolvedTypeReference(somethingtype);
            const opttype = this.m_assembly.getOptionConceptType(linfo);
            const miropttype = this.m_emitter.registerResolvedTypeReference(opttype);

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNothing(), ValueType.createUniform(this.m_assembly.getSpecialNothingType()), opttype), trgt, this.m_emitter.registerResolvedTypeReference(linfo), undefined);

            const loadreg = this.m_emitter.generateTmpRegister();
            const hasreg = this.m_emitter.generateTmpRegister();
            const guard = new MIRArgGuard(hasreg);
            this.m_emitter.emitLoadTupleIndexSetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), loadreg, guard);
            
            this.m_emitter.emitGuardedOptionInject(op.sinfo, this.m_emitter.registerResolvedTypeReference(linfo), mirsomethingtype, miropttype, loadreg, trgt, new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            
            return env.setUniformResultExpression(opttype);
        }
    }

    private checkPostfixGetIndexTryMulti(env: ExpressionTypeEnvironment, op: PostfixGetIndexTry, arg: MIRRegisterArgument): ExpressionTypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isTupleTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasIndex(op.sinfo, texp.flowtype, op.idx);
        if (hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
        }
        else if (hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.idx);

            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadTupleIndex(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), lreg);
            const aenv = this.checkAssignSingleVariable(op.sinfo, env, op.vname, ValueType.createUniform(linfo), lreg);

            this.m_emitter.emitLoadConstBool(op.sinfo, true, trgt);
            return [aenv.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else {
            const linfo = this.getInfoForLoadFromSafeIndex(op.sinfo, texp.flowtype, op.idx);

            this.m_emitter.emitLoadTupleIndexSetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.idx, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), new MIRRegisterArgument(op.vname), new MIRArgGuard(trgt));
            return [
                env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False),
                env.setVar(op.vname, linfo).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)
            ];
        }
    }

    private checkPostfixGetIndexTryMono(env: ExpressionTypeEnvironment, op: PostfixGetIndexTry, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        return ExpressionTypeEnvironment.join(this.m_assembly, ...this.checkPostfixGetIndexTryMulti(env, op, arg, trgt));
    }

    private checkPostfixHasPropertyMulti(env: ExpressionTypeEnvironment, op: PostfixHasProperty, arg: MIRRegisterArgument): ExpressionTypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Can only check for properties on record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.pname);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            this.m_emitter.emitLoadConstBool(op.sinfo, true, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else {
            assert(!texp.flowtype.isUniqueRecordTargetType(), "If this is unique then we should have been in one of the cases above");

            this.m_emitter.emitRecordHasProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, trgt);

            const renvs = ExpressionTypeEnvironment.convertToHasIndexNotHasPropertyFlowsOnResult(this.m_assembly, op.pname, [env]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
    }

    private checkPostfixHasPropertyMono(env: ExpressionTypeEnvironment, op: PostfixHasProperty, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        return ExpressionTypeEnvironment.join(this.m_assembly, ...this.checkPostfixHasPropertyMulti(env, op, arg, trgt));
    }

    private checkPostfixGetPropertyOrNone(env: ExpressionTypeEnvironment, op: PostfixGetPropertyOrNone, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Can only load properties from record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.pname);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstNone(op.sinfo, trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialNoneType());
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeProperty(op.sinfo, texp.flowtype, op.pname);

            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), trgt);
            return env.setUniformResultExpression(linfo);
        }
        else {
            const rtype = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp.flowtype, op.pname);
            const linfo = this.m_assembly.typeUpperBound([this.m_assembly.getSpecialNoneType(), rtype]);

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNone(), ValueType.createUniform(this.m_assembly.getSpecialNoneType()), linfo), trgt, this.m_emitter.registerResolvedTypeReference(linfo), undefined);

            const loadreg = this.m_emitter.generateTmpRegister();
            const hasreg = this.m_emitter.generateTmpRegister();
            const guard = new MIRArgGuard(hasreg);
            this.m_emitter.emitLoadRecordPropertySetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(rtype), loadreg, guard);
            if(rtype.isSameType(linfo)) {
                this.m_emitter.emitRegisterStore(op.sinfo, loadreg, trgt, this.m_emitter.registerResolvedTypeReference(linfo), new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            }
            else {
                this.m_emitter.emitConvert(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtype), this.m_emitter.registerResolvedTypeReference(rtype), this.m_emitter.registerResolvedTypeReference(linfo), loadreg, trgt, new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            }

            return env.setUniformResultExpression(linfo);
        }
    }

    private checkPostfixGetPropertyOption(env: ExpressionTypeEnvironment, op: PostfixGetPropertyOption, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Can only load indecies from tuple types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.pname);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstNothing(op.sinfo, trgt);
            return env.setUniformResultExpression(this.m_assembly.getSpecialNothingType());
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp.flowtype, op.pname);
            const somethingtype = this.m_assembly.getSomethingType(linfo);
            const mirsomethingtype = this.m_emitter.registerResolvedTypeReference(somethingtype);

            const loadreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), loadreg);
            this.m_emitter.emitInject(op.sinfo, this.m_emitter.registerResolvedTypeReference(linfo), mirsomethingtype, loadreg, trgt);

            return env.setUniformResultExpression(somethingtype);
        }
        else {
            const linfo = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp.flowtype, op.pname);
            const somethingtype = this.m_assembly.getSomethingType(linfo);
            const mirsomethingtype = this.m_emitter.registerResolvedTypeReference(somethingtype);
            const opttype = this.m_assembly.getOptionConceptType(linfo);
            const miropttype = this.m_emitter.registerResolvedTypeReference(opttype);

            this.m_emitter.emitRegisterStore(op.sinfo, this.emitInlineConvertIfNeeded(op.sinfo, new MIRConstantNothing(), ValueType.createUniform(this.m_assembly.getSpecialNothingType()), opttype), trgt, this.m_emitter.registerResolvedTypeReference(linfo), undefined);

            const loadreg = this.m_emitter.generateTmpRegister();
            const hasreg = this.m_emitter.generateTmpRegister();
            const guard = new MIRArgGuard(hasreg);
            this.m_emitter.emitLoadRecordPropertySetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), loadreg, guard);
            
            this.m_emitter.emitGuardedOptionInject(op.sinfo, this.m_emitter.registerResolvedTypeReference(linfo), mirsomethingtype, miropttype, loadreg, trgt, new MIRStatmentGuard(guard, "defaultonfalse", trgt));
            
            return env.setUniformResultExpression(opttype);
        }
    }

    private checkPostfixGetPropertyTryMulti(env: ExpressionTypeEnvironment, op: PostfixGetPropertyTry, arg: MIRRegisterArgument): ExpressionTypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;
        this.raiseErrorIf(op.sinfo, !texp.flowtype.isRecordTargetType(), "Can only load properties from record types");

        const hpi = this.getInfoForHasProperty(op.sinfo, texp.flowtype, op.pname);
        if(hpi === "no") {
            this.m_emitter.emitLoadConstBool(op.sinfo, false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)];
        }
        else if(hpi === "yes") {
            const linfo = this.getInfoForLoadFromSafeProperty(op.sinfo, texp.flowtype, op.pname);

            const lreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitLoadProperty(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueRecordTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), lreg);
            const aenv = this.checkAssignSingleVariable(op.sinfo, env, op.vname, ValueType.createUniform(linfo), lreg);

            this.m_emitter.emitLoadConstBool(op.sinfo, true, trgt);
            return [aenv.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)];
        }
        else {
            const linfo = this.getInfoForLoadFromSafePropertyOnly(op.sinfo, texp.flowtype, op.pname);
            
            this.m_emitter.emitLoadRecordPropertySetGuard(op.sinfo, arg, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), op.pname, !texp.flowtype.isUniqueTupleTargetType(), this.m_emitter.registerResolvedTypeReference(linfo), new MIRRegisterArgument(op.vname), new MIRArgGuard(trgt));
            return [
                env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False),
                env.setVar(op.vname, linfo).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True)
            ];
        }
    }

    private checkPostfixGetPropertyTryMono(env: ExpressionTypeEnvironment, op: PostfixGetPropertyTry, arg: MIRRegisterArgument): ExpressionTypeEnvironment {
        return ExpressionTypeEnvironment.join(this.m_assembly, ...this.checkPostfixGetPropertyTryMulti(env, op, arg, trgt));
    }

    private checkInvokeMulti(env: ExpressionTypeEnvironment, op: PostfixInvoke, arg: MIRRegisterArgument, trgt: MIRRegisterArgument, refok: boolean): ExpressionTypeEnvironment[] {
        const texp = env.getExpressionResult().valtype;

        const resolvefrom = op.specificResolve !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.specificResolve, env.terms) : texp.flowtype;
        const knownimpl_multi = this.m_assembly.tryGetMethodUniqueConcreteDeclFromType(resolvefrom, op.name);
        const vinfo_multi = this.m_assembly.tryGetMethodUniqueRootDeclFromType(texp.flowtype, op.name);

        if(knownimpl_multi !== undefined && knownimpl_multi.decl.length > 1) {
            //
            //TODO: Big hack workaround for static overloading -- need to implement in general but we really need it for some container functions with functor options
            //

            let eev = env;
            if (op.isBinder) {
                eev = this.checkDeclareSingleVariableBinder(op.sinfo, env, `$this_@${op.sinfo.pos}`, texp, arg);
            }

            const hackpc = this.getLambdaArgCount_Hack(env, op.args);
            this.raiseErrorIf(op.sinfo, hackpc === -1, "Could not get specialization info for resolution");
            
            const knownimpl_find = knownimpl_multi.decl.find((ki) => {
                const lp = ki.invoke.params.find((pp) => pp.type instanceof FunctionTypeSignature);
                return lp !== undefined && (lp.type as FunctionTypeSignature).params.length === hackpc;
            });
            assert(knownimpl_find !== undefined);

            const knownimpl = new OOMemberLookupInfo<MemberMethodDecl>(knownimpl_multi.contiainingType, knownimpl_find as MemberMethodDecl, knownimpl_multi.binds);
            const selfvar = [texp, knownimpl.decl.refRcvr ? env.getExpressionResult().expvar : undefined, arg] as [ValueType, string | undefined, MIRRegisterArgument];
            const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, knownimpl.decl.invoke, op.terms.targs, knownimpl.binds, env.terms, selfvar, refok);
            this.checkTemplateTypes(op.sinfo, knownimpl.decl.invoke.terms, callbinds, knownimpl.decl.invoke.termRestrictions);

            const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
            this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.rec);

            const ootyperesolved = this.resolveOOTypeFromDecls(knownimpl.contiainingType, knownimpl.binds);
            const ootype = this.m_emitter.registerResolvedTypeReference(ootyperesolved);
            const ckey = this.m_emitter.registerMethodCall(ootyperesolved, [ootype, knownimpl.contiainingType, knownimpl.binds], knownimpl.decl, op.name, callbinds, rargs.pcodes, rargs.cinfo);
            const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
            this.m_emitter.emitInvokeFixedFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);

            if (op.isBinder) {
                this.m_emitter.localLifetimeEnd(op.sinfo, `$this_@${op.sinfo.pos}`)
            }

            return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
        }
        else {
            if (knownimpl_multi !== undefined) {
                const knownimpl = new OOMemberLookupInfo<MemberMethodDecl>(knownimpl_multi.contiainingType, knownimpl_multi.decl[0], knownimpl_multi.binds);

                if(knownimpl.decl.invoke.body !== undefined && (typeof(knownimpl.decl.invoke.body.body) === "string") && ["special_nothing", "special_something", "special_extract"].includes(knownimpl.decl.invoke.body.body as string)) {
                    this.raiseErrorIf(op.sinfo, op.args.argList.length !== 0, "No arguments permitted on this method");
                    
                    const sinv = knownimpl.decl.invoke.body.body as string;
                    if(sinv === "special_nothing") {
                        return this.checkIsTypeExpression_commondirect(op.sinfo, env, arg, this.m_assembly.getSpecialNothingType(), trgt);
                    }
                    else if(sinv === "special_something") {
                        return this.checkIsTypeExpression_commondirect(op.sinfo, env, arg, this.m_assembly.getSpecialISomethingConceptType(), trgt);
                    }
                    else {
                        const restype = this.resolveAndEnsureTypeOnly(op.sinfo, knownimpl.decl.invoke.resultType, knownimpl.binds);
                        const mirrestype = this.m_emitter.registerResolvedTypeReference(restype);
                        const ctype = this.resolveOOTypeFromDecls(knownimpl.contiainingType, knownimpl.binds);
                        const mirctype = this.m_emitter.registerResolvedTypeReference(ctype);

                        const arge = this.emitInlineConvertIfNeeded(op.sinfo, arg, env.getExpressionResult().valtype, ctype);
                        this.m_emitter.emitExtract(op.sinfo, mirctype, mirrestype, arge, trgt);

                        return [env.setUniformResultExpression(restype)];
                    }
                }
                else {
                    let eev = env;
                    if (op.isBinder) {
                        eev = this.checkDeclareSingleVariableBinder(op.sinfo, env, `$this_@${op.sinfo.pos}`, texp, arg);
                    }

                    const selfvar = [texp, knownimpl.decl.refRcvr ? env.getExpressionResult().expvar : undefined, arg] as [ValueType, string | undefined, MIRRegisterArgument];
                    const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, knownimpl.decl.invoke, op.terms.targs, knownimpl.binds, env.terms, selfvar, refok);
                    this.checkTemplateTypes(op.sinfo, knownimpl.decl.invoke.terms, callbinds, knownimpl.decl.invoke.termRestrictions);

                    const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
                    this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.rec);

                    const ootyperesolved = this.resolveOOTypeFromDecls(knownimpl.contiainingType, knownimpl.binds);
                    const ootype = this.m_emitter.registerResolvedTypeReference(ootyperesolved);
                    const ckey = this.m_emitter.registerMethodCall(ootyperesolved, [ootype, knownimpl.contiainingType, knownimpl.binds], knownimpl.decl, op.name, callbinds, rargs.pcodes, rargs.cinfo);
                    const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                    this.m_emitter.emitInvokeFixedFunction(op.sinfo, ckey, rargs.args, rargs.fflag, refinfo, trgt);

                    if (op.isBinder) {
                        this.m_emitter.localLifetimeEnd(op.sinfo, `$this_@${op.sinfo.pos}`)
                    }

                    return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
                }
            }
            else {
                this.raiseErrorIf(op.sinfo, vinfo_multi === undefined, 
                    
                    `Missing (or multiple possible) declarations of "${op.name}" method on receiver type "${texp.flowtype.typeID}"`);

                let eev = env;
                if (op.isBinder) {
                    eev = this.checkDeclareSingleVariableBinder(op.sinfo, env, `$this_@${op.sinfo.pos}`, texp, arg);
                }

                const vinfo = vinfo_multi as OOMemberLookupInfo<MemberMethodDecl[]>;
                const minfo = new OOMemberLookupInfo<MemberMethodDecl>(vinfo.contiainingType, vinfo.decl[0], vinfo.binds);

                const selfvar = [texp, minfo.decl.refRcvr ? env.getExpressionResult().expvar : undefined, arg] as [ValueType, string | undefined, MIRRegisterArgument];
                const [fsig, callbinds, eargs] = this.inferAndCheckArguments(op.sinfo, eev, op.args, minfo.decl.invoke, op.terms.targs, minfo.binds, env.terms, selfvar, refok);
                this.checkTemplateTypes(op.sinfo, minfo.decl.invoke.terms, callbinds, minfo.decl.invoke.termRestrictions);

                const rargs = this.checkArgumentsSignature(op.sinfo, eev, op.name, fsig, eargs);
                this.checkRecursion(op.sinfo, fsig, rargs.pcodes, op.rec);

                const ootype = this.resolveOOTypeFromDecls(minfo.contiainingType, minfo.binds);
                const ckey = this.m_emitter.registerVirtualMethodCall(ootype, op.name, callbinds, rargs.pcodes, rargs.cinfo);
                const refinfo = this.generateRefInfoForCallEmit(fsig as ResolvedFunctionType, rargs.refs);
                this.m_emitter.emitInvokeVirtualFunction(op.sinfo, ckey.keyid, ckey.shortname, this.m_emitter.registerResolvedTypeReference(texp.layout), this.m_emitter.registerResolvedTypeReference(texp.flowtype), rargs.args, rargs.fflag, refinfo, trgt);

                if (op.isBinder) {
                    this.m_emitter.localLifetimeEnd(op.sinfo, `$this_@${op.sinfo.pos}`)
                }

                return this.updateEnvForOutParams(env.setUniformResultExpression(fsig.resultType), rargs.refs);
            }
        }
    }

    private checkInvokeMono(env: ExpressionTypeEnvironment, op: PostfixInvoke, arg: MIRRegisterArgument, trgt: MIRRegisterArgument, refok: boolean): ExpressionTypeEnvironment {
        return ExpressionTypeEnvironment.join(this.m_assembly, ...this.checkInvokeMulti(env, op, arg, trgt, refok));
    }

    private checkPostfixExpression(env: ExpressionTypeEnvironment, exp: PostfixOp, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): ExpressionTypeEnvironment[] {
        let etgrt = this.m_emitter.generateTmpRegister();
        let itype = (exp.ops.length !== 0 && exp.ops[0] instanceof PostfixAs) ? this.resolveAndEnsureTypeOnly((exp.ops[0] as PostfixAs).sinfo, (exp.ops[0] as PostfixAs).astype, env.terms) : undefined;
        let cenv = this.checkExpression(env, exp.rootExp, etgrt, itype, {refok: refok, orok: false});

        let lenv: ExpressionTypeEnvironment[] = [];
        for (let i = 0; i < exp.ops.length; ++i) {
            const lastop = (i + 1 === exp.ops.length);
            const itype = lastop ? infertype : ((exp.ops[i + 1] instanceof PostfixAs) ? this.resolveAndEnsureTypeOnly((exp.ops[i + 1] as PostfixAs).sinfo, (exp.ops[i + 1] as PostfixAs).astype, cenv.terms) : undefined);

            const ntgrt = this.m_emitter.generateTmpRegister();
            switch (exp.ops[i].op) {
                case PostfixOpTag.PostfixAccessFromIndex:
                    cenv = this.checkAccessFromIndex(cenv, exp.ops[i] as PostfixAccessFromIndex, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixProjectFromIndecies:
                    cenv = this.checkProjectFromIndecies(cenv, exp.ops[i] as PostfixProjectFromIndecies, etgrt, ntgrt, itype);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixAccessFromName:
                    cenv = this.checkAccessFromName(cenv, exp.ops[i] as PostfixAccessFromName, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixProjectFromNames:
                    cenv = this.checkProjectFromNames(cenv, exp.ops[i] as PostfixProjectFromNames, etgrt, ntgrt, itype);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixModifyWithIndecies:
                    cenv = this.checkModifyWithIndecies(cenv, exp.ops[i] as PostfixModifyWithIndecies, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixModifyWithNames:
                    cenv = this.checkModifyWithNames(cenv, exp.ops[i] as PostfixModifyWithNames, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixIs:
                    if (!lastop) {
                        cenv = this.checkPostfixIsMono(cenv, exp.ops[i] as PostfixIs, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixIsMulti(cenv, exp.ops[i] as PostfixIs, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixAs:
                    cenv = this.checkPostfixAs(cenv, exp.ops[i] as PostfixAs, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixHasIndex:
                    if (!lastop) {
                        cenv = this.checkPostfixHasIndexMono(cenv, exp.ops[i] as PostfixHasIndex, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixHasIndexMulti(cenv, exp.ops[i] as PostfixHasIndex, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixHasProperty:
                    if (!lastop) {
                        cenv = this.checkPostfixHasPropertyMono(cenv, exp.ops[i] as PostfixHasProperty, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixHasPropertyMulti(cenv, exp.ops[i] as PostfixHasProperty, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixGetIndexOrNone:
                    cenv = this.checkPostfixGetIndexOrNone(cenv, exp.ops[i] as PostfixGetIndexOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixGetIndexOption:
                    cenv = this.checkPostfixGetIndexOption(cenv, exp.ops[i] as PostfixGetIndexOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixGetIndexTry:
                    if (!lastop) {
                        cenv = this.checkPostfixGetIndexTryMono(cenv, exp.ops[i] as PostfixGetIndexTry, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixGetIndexTryMulti(cenv, exp.ops[i] as PostfixGetIndexTry, etgrt, ntgrt);
                    }
                    break;
                case PostfixOpTag.PostfixGetPropertyOrNone:
                    cenv = this.checkPostfixGetPropertyOrNone(cenv, exp.ops[i] as PostfixGetPropertyOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixGetPropertyOption:
                    cenv = this.checkPostfixGetPropertyOption(cenv, exp.ops[i] as PostfixGetPropertyOrNone, etgrt, ntgrt);
                    lenv = [cenv];
                    break;
                case PostfixOpTag.PostfixHasProperty:
                    if (!lastop) {
                        cenv = this.checkPostfixGetPropertyTryMono(cenv, exp.ops[i] as PostfixGetPropertyTry, etgrt, ntgrt);
                    }
                    else {
                        lenv = this.checkPostfixGetPropertyTryMulti(cenv, exp.ops[i] as PostfixGetPropertyTry, etgrt, ntgrt);
                    }
                    break;
                default:
                    this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== PostfixOpTag.PostfixInvoke, "Unknown postfix op");
                    if (!lastop) {
                        cenv = this.checkInvokeMono(cenv, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, refok);
                    }
                    else {
                        lenv = this.checkInvokeMulti(cenv, exp.ops[i] as PostfixInvoke, etgrt, ntgrt, refok);
                    }
                    break;
            }

            etgrt = ntgrt;
        }

        if (lenv.length === 0) {
            return [];
        }
        else {
            const lasttype = ValueType.join(this.m_assembly, ...lenv.map((ee) => ee.getExpressionResult().valtype));
            this.m_emitter.emitRegisterStore(exp.sinfo, etgrt, trgt, this.m_emitter.registerResolvedTypeReference(lasttype.layout), undefined);

            return lenv;
        }
    }

    private checkPrefixNotOp(env: ExpressionTypeEnvironment, exp: PrefixNotOp, trgt: MIRRegisterArgument, refok: boolean): ExpressionTypeEnvironment[] {
        const etreg = this.m_emitter.generateTmpRegister();
        const estates = this.checkExpressionMultiFlow(env, exp.exp, etreg, this.m_assembly.getSpecialBoolType(), {refok: refok, orok: false});

        this.m_emitter.emitPrefixNotOp(exp.sinfo, etreg, trgt);

        const bstates = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, estates);
        const ntstates = bstates.fenvs.map((state) => state.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));
        const nfstates = bstates.tenvs.map((state) => state.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));

        return [...ntstates, ...nfstates];
    }

    private strongEQ(sinfo: SourceInfo, env: ExpressionTypeEnvironment, lhsarg: Expression, rhsarg: Expression): ExpressionTypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, lhsarg, lhsreg, undefined);
        let olhs = lhs.getExpressionResult().valtype;

        const rhsreg = this.m_emitter.generateTmpRegister();
        const rhs = this.checkExpression(env, rhsarg, rhsreg, undefined);
        let orhs = rhs.getExpressionResult().valtype;

        const action = this.checkValueEq(lhsarg, lhs.getExpressionResult().valtype.flowtype, rhsarg, rhs.getExpressionResult().valtype.flowtype);
        this.raiseErrorIf(sinfo, action === "err", "Compared types are not equivalent (or not unique modulo none)");

        if(action === "truealways" || action === "falsealways") {
            this.m_emitter.emitLoadConstBool(sinfo, action === "truealways" ? true : false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), action === "truealways" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
        }
        else if (action === "lhsnone") {
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            
            const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [rhs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "rhsnone") {
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            
            const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "lhsnothing") {
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            
            const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [rhs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "rhsnothing") {
            this.m_emitter.emitTypeOf(sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            
            const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [lhs]);
            return [
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else {
            if (action === "lhssomekey") {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

                const oftypereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), rhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), this.m_emitter.registerResolvedTypeReference(orhs.flowtype), undefined);
                
                const sguard = new MIRStatmentGuard(new MIRArgGuard(oftypereg), "defaultonfalse", new MIRConstantFalse());
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), trgt, sguard, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));
                
                const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [rhs]);
                return [
                    ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                    ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
                ];
            }
            else if (action === "rhssomekey") {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

                const oftypereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(orhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(olhs.layout), this.m_emitter.registerResolvedTypeReference(olhs.flowtype), undefined);
                
                const sguard = new MIRStatmentGuard(new MIRArgGuard(oftypereg), "defaultonfalse", new MIRConstantFalse());
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(orhs.flowtype), trgt, sguard, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));

                const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
                return [
                    ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                    ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
                ];
            }
            else {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), trgt, undefined, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));

                return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)];
            }
        }
    }

    private strongNEQ(sinfo: SourceInfo, env: ExpressionTypeEnvironment, lhsarg: Expression, rhsarg: Expression): ExpressionTypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpression(env, lhsarg, lhsreg, undefined);
        let olhs = lhs.getExpressionResult().valtype;

        const rhsreg = this.m_emitter.generateTmpRegister();
        const rhs = this.checkExpression(env, rhsarg, rhsreg, undefined);
        let orhs = rhs.getExpressionResult().valtype;

        const action = this.checkValueEq(lhsarg, lhs.getExpressionResult().valtype.flowtype, rhsarg, rhs.getExpressionResult().valtype.flowtype);
        this.raiseErrorIf(sinfo, action === "err", "Compared types are not equivalent (or not unique modulo none)");

        if(action === "truealways" || action === "falsealways") {
            this.m_emitter.emitLoadConstBool(sinfo, action === "falsealways" ? true : false, trgt);
            return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), action === "falsealways" ? FlowTypeTruthValue.True : FlowTypeTruthValue.False)];
        }
        else if (action === "lhsnone") {
            //note use of negation here
            const oftypereg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            this.m_emitter.emitPrefixNotOp(sinfo, oftypereg, trgt);

            const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [rhs]);
            return [
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "rhsnone") {
            //note use of negation here
            const oftypereg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            this.m_emitter.emitPrefixNotOp(sinfo, oftypereg, trgt);

            const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
            return [
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "lhsnothing") {
            //note use of negation here
            const oftypereg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), rhsreg, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().valtype.flowtype), undefined);
            this.m_emitter.emitPrefixNotOp(sinfo, oftypereg, trgt);

            const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [rhs]);
            return [
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else if (action === "rhsnothing") {
            //note use of negation here
            const oftypereg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNothingType()), lhsreg, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.layout), this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().valtype.flowtype), undefined);
            this.m_emitter.emitPrefixNotOp(sinfo, oftypereg, trgt);

            const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNothingType(), [lhs]);
            return [
                ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True))),
                ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False)))
            ];
        }
        else {
            if (action === "lhssomekey") {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

                const oftypereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), rhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), this.m_emitter.registerResolvedTypeReference(orhs.flowtype), undefined);
    
                const sguard = new MIRStatmentGuard(new MIRArgGuard(oftypereg), "defaultonfalse", new MIRConstantFalse());
                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), treg, sguard, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));
                this.m_emitter.emitPrefixNotOp(sinfo, treg, trgt);

                const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [rhs]);
                return [
                    ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                    ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
                ];
            }
            else if (action === "rhssomekey") {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

                const oftypereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitTypeOf(sinfo, oftypereg, this.m_emitter.registerResolvedTypeReference(orhs.flowtype), lhsreg, this.m_emitter.registerResolvedTypeReference(olhs.layout), this.m_emitter.registerResolvedTypeReference(olhs.flowtype), undefined);
                
                const sguard = new MIRStatmentGuard(new MIRArgGuard(oftypereg), "defaultonfalse", new MIRConstantFalse());
                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(orhs.flowtype), treg, sguard, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));
                this.m_emitter.emitPrefixNotOp(sinfo, treg, trgt);

                const renvs = ExpressionTypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), [lhs]);
                return [
                    ...(renvs.fenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False))),
                    ...(renvs.tenvs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)))
                ];
            }
            else {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(olhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !olhs.flowtype.isGroundedType(), "Type must be grounded");

                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(orhs.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()), "Type must be KeyType");
                this.raiseErrorIf(sinfo, !orhs.flowtype.isGroundedType(), "Type must be grounded");

                const treg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitBinKeyEq(sinfo, this.m_emitter.registerResolvedTypeReference(olhs.layout), lhsreg, this.m_emitter.registerResolvedTypeReference(orhs.layout), rhsreg, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), treg, undefined, this.m_emitter.registerResolvedTypeReference(olhs.flowtype), this.m_emitter.registerResolvedTypeReference(orhs.flowtype));
                this.m_emitter.emitPrefixNotOp(sinfo, treg, trgt);

                return [env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.Unknown)];
            }
        }
    }

    private checkBinLogic(env: ExpressionTypeEnvironment, exp: BinLogicExpression, trgt: MIRRegisterArgument, refok: boolean): ExpressionTypeEnvironment[] {
        const lhsreg = this.m_emitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg, undefined, { refok: refok, orok: false });

        this.raiseErrorIf(exp.sinfo, lhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
        const blhsreg = this.emitInlineConvertToFlow(exp.sinfo, lhsreg, ValueType.join(this.m_assembly, ...lhs.map((eev) => eev.getExpressionResult().valtype)));

        if (exp.op === "||") {
            if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.True)) {
                this.m_emitter.emitLoadConstBool(exp.sinfo, true, trgt);
                return lhs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
            }
            else {
                const doneblck = this.m_emitter.createNewBlock("Llogic_or_done");
                const restblck = this.m_emitter.createNewBlock("Llogic_or_rest");

                const fflows = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);

                this.m_emitter.emitRegisterStore(exp.sinfo, blhsreg, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);
                this.m_emitter.emitBoolJump(exp.sinfo, blhsreg, doneblck, restblck);
                this.m_emitter.setActiveBlock(restblck);

                const rhsreg = this.m_emitter.generateTmpRegister();
                const rhs = this.checkExpressionMultiFlow(ExpressionTypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.rhs, rhsreg, undefined, { refok: refok, orok: false });

                this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertToFlow(exp.sinfo, rhsreg, ValueType.join(this.m_assembly, ...rhs.map((eev) => eev.getExpressionResult().valtype))), trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);

                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.setActiveBlock(doneblck);

                const oflows = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                return [...fflows.tenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), eev.getExpressionResult().truthval));
            }
        }
        else if (exp.op === "&&") {
            if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.False)) {
                this.m_emitter.emitLoadConstBool(exp.sinfo, false, trgt);
                return lhs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));
            }
            else {
                const doneblck = this.m_emitter.createNewBlock("Llogic_and_done");
                const restblck = this.m_emitter.createNewBlock("Llogic_and_rest");

                const fflows = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);

                this.m_emitter.emitRegisterStore(exp.sinfo, blhsreg, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);
                this.m_emitter.emitBoolJump(exp.sinfo, blhsreg, restblck, doneblck);
                this.m_emitter.setActiveBlock(restblck);

                const rhsreg = this.m_emitter.generateTmpRegister();
                const rhs = this.checkExpressionMultiFlow(ExpressionTypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.rhs, rhsreg, undefined, { refok: refok, orok: false });

                this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertToFlow(exp.sinfo, rhsreg, ValueType.join(this.m_assembly, ...rhs.map((eev) => eev.getExpressionResult().valtype))), trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);

                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.setActiveBlock(doneblck);
                const oflows = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                return [...fflows.fenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), eev.getExpressionResult().truthval));
            }
        }
        else {
            if (lhs.every((ee) => ee.getExpressionResult().truthval === FlowTypeTruthValue.False)) {
                this.m_emitter.emitLoadConstBool(exp.sinfo, true, trgt);
                return lhs.map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
            }
            else {
                const doneblck = this.m_emitter.createNewBlock("Llogic_imply_done");
                const restblck = this.m_emitter.createNewBlock("Llogic_imply_rest");

                const fflows = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, lhs);

                this.m_emitter.emitPrefixNotOp(exp.sinfo, blhsreg, trgt);
                this.m_emitter.emitBoolJump(exp.sinfo, blhsreg, restblck, doneblck);
                this.m_emitter.setActiveBlock(restblck);

                const rhsreg = this.m_emitter.generateTmpRegister();
                const rhs = this.checkExpressionMultiFlow(ExpressionTypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.rhs, rhsreg, undefined, { refok: refok, orok: false });

                this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
                this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertToFlow(exp.sinfo, rhsreg, ValueType.join(this.m_assembly, ...rhs.map((eev) => eev.getExpressionResult().valtype))), trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), undefined);

                this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.setActiveBlock(doneblck);

                const oflows = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, rhs);
                return [...fflows.fenvs, ...oflows.tenvs, ...oflows.fenvs].map((eev) => eev.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), eev.getExpressionResult().truthval));
            }
        }
    }

    private checkMapEntryConstructorExpression(env: ExpressionTypeEnvironment, exp: MapEntryConstructorExpression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const itype = infertype !== undefined ? infertype.tryGetInferrableTupleConstructorType() : undefined;
        const metype = (itype !== undefined && itype.types.length === 2) ? itype : undefined;

        const kreg = this.m_emitter.generateTmpRegister();
        const kinfer = metype !== undefined ? metype.types[0] : undefined;
        const ktype = this.checkExpression(env, exp.kexp, kreg, kinfer).getExpressionResult().valtype;

        this.raiseErrorIf(exp.kexp.sinfo, !this.m_assembly.subtypeOf(ktype.flowtype, this.m_assembly.getSpecialKeyTypeConceptType()) || !ktype.flowtype.isGroundedType(), "Key must be a grounded KeyType value");

        const vreg = this.m_emitter.generateTmpRegister();
        const vinfer = metype !== undefined ? metype.types[1] : undefined;
        const vtype = this.checkExpression(env, exp.vexp, vreg, vinfer).getExpressionResult().valtype;

        const mtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([ktype.flowtype, vtype.flowtype]));

        const targs = [ this.emitInlineConvertToFlow(exp.sinfo, kreg, ktype), this.emitInlineConvertToFlow(exp.sinfo, vreg, vtype)];
        this.m_emitter.emitConstructorTuple(exp.sinfo, this.m_emitter.registerResolvedTypeReference(mtype), targs, trgt);

        return env.setUniformResultExpression(mtype);
    }

    private checkSelect(env: ExpressionTypeEnvironment, exp: SelectExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const testreg = this.m_emitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, exp.test, testreg, undefined, { refok: refok, orok: false });

        this.raiseErrorIf(exp.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");
        const btestreg = this.emitInlineConvertToFlow(exp.sinfo, testreg, ValueType.createUniform(this.m_assembly.getSpecialBoolType()));

        const fflows = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);

        if(fflows.tenvs.length === 0) {
            return this.checkExpression(ExpressionTypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.option2, trgt, infertype);
        }
        else if (fflows.fenvs.length === 0) {
            return this.checkExpression(ExpressionTypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.option1, trgt, infertype);
        }
        else {
            const doneblck = this.m_emitter.createNewBlock("Lselect_done");
            const trueblck = this.m_emitter.createNewBlock("Lselect_true");
            const falseblck = this.m_emitter.createNewBlock("Lselect_false");

            this.m_emitter.emitBoolJump(exp.sinfo, btestreg, trueblck, falseblck);

            this.m_emitter.setActiveBlock(trueblck);
            const truereg = this.m_emitter.generateTmpRegister();
            const truestate = this.checkExpression(ExpressionTypeEnvironment.join(this.m_assembly, ...fflows.tenvs), exp.option1, truereg, infertype);
            //note jump isn't set yet

            this.m_emitter.setActiveBlock(falseblck);
            const falsereg = this.m_emitter.generateTmpRegister();
            const falsestate = this.checkExpression(ExpressionTypeEnvironment.join(this.m_assembly, ...fflows.fenvs), exp.option2, falsereg, infertype);
            //note jump isn't set yet

            const fulltype = this.m_assembly.typeUpperBound([truestate.getExpressionResult().valtype.flowtype, falsestate.getExpressionResult().valtype.flowtype]);

            //set the assigns and jumps
            this.m_emitter.setActiveBlock(trueblck);
            this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, truereg, truestate.getExpressionResult().valtype, fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.setActiveBlock(falseblck);
            this.m_emitter.emitRegisterStore(exp.sinfo, this.emitInlineConvertIfNeeded(exp.sinfo, falsereg, falsestate.getExpressionResult().valtype, fulltype), trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);
            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);

            this.m_emitter.setActiveBlock(doneblck);

            return ExpressionTypeEnvironment.join(this.m_assembly, ...[truestate, falsestate].map((eev) => eev.updateResultExpression(fulltype, eev.getExpressionResult().valtype.flowtype)));
        }
    }

    private checkBlockExpression(env: ExpressionTypeEnvironment, exp: BlockStatementExpression, infertype: ResolvedType | undefined): ExpressionTypeEnvironment {
        try {
            this.m_emitter.processEnterYield();
            let cenv = env.freezeVars(infertype).pushLocalScope();

            for (let i = 0; i < exp.ops.length; ++i) {
                if (!cenv.hasNormalFlow()) {
                    break;
                }

                cenv = this.checkStatement(cenv, exp.ops[i]);
            }

            const yblck = this.m_emitter.createNewBlock("Lyield");
            if (cenv.hasNormalFlow()) {
                this.m_emitter.setActiveBlock(yblck);

                const deadvars = cenv.getCurrentFrameNames();
                for (let i = 0; i < deadvars.length; ++i) {
                    this.m_emitter.localLifetimeEnd(exp.sinfo, deadvars[i]);
                }
            }

            this.raiseErrorIf(exp.sinfo, cenv.hasNormalFlow(), "Not all flow paths yield a value!");
            this.raiseErrorIf(exp.sinfo, cenv.yieldResult === undefined, "No valid flow through expresssion block");

            const ytype = cenv.yieldResult as ResolvedType;
            const yeildcleanup = this.m_emitter.getActiveYieldSet();
            if (cenv.hasNormalFlow()) {
                for (let i = 0; i < yeildcleanup.length; ++i) {
                    const yci = yeildcleanup[i];
                    this.m_emitter.setActiveBlock(yci[0]);

                    const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, yci[1], yci[2], ytype);
                    this.m_emitter.emitRegisterStore(exp.sinfo, convreg, trgt, this.m_emitter.registerResolvedTypeReference(ytype), undefined);

                    this.m_emitter.emitDirectJump(exp.sinfo, yblck);
                }
            }

            return env.setUniformResultExpression(ytype);
        }
        finally {
            this.m_emitter.processExitYield();
        }
    }

    private checkIfExpression(env: ExpressionTypeEnvironment, exp: IfExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const doneblck = this.m_emitter.createNewBlock("Lifexp_done");

        let cenv = env;
        let hasfalseflow = true;
        let results: ExpressionTypeEnvironment[] = [];
        let rblocks: [string, MIRRegisterArgument, ValueType][] = [];

        for (let i = 0; i < exp.flow.conds.length && hasfalseflow; ++i) {
            const testreg = this.m_emitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, exp.flow.conds[i].cond, testreg, infertype, i === 0 ? { refok: refok, orok: false } : undefined);
            this.raiseErrorIf(exp.sinfo, !test.every((eev) => this.m_assembly.subtypeOf(eev.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "If test expression must return a Bool");

            const cflow = ExpressionTypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
            
            if (cflow.tenvs.length === 0) {
                //can just keep generating tests in striaght line
                cenv = ExpressionTypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
            else if (cflow.fenvs.length === 0) {
                //go though true block (without jump) and then skip else
                const trueblck = this.m_emitter.createNewBlock(`Lifexp_${i}true`);
                this.m_emitter.emitDirectJump(exp.sinfo, trueblck);
                this.m_emitter.setActiveBlock(trueblck);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(ExpressionTypeEnvironment.join(this.m_assembly, ...cflow.tenvs), exp.flow.conds[i].action, ttreg, infertype);
                
                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype]);
                hasfalseflow = false;
            }
            else {
                const trueblck = this.m_emitter.createNewBlock(`Lifexp_${i}true`);
                const falseblck = this.m_emitter.createNewBlock(`Lifexp_${i}false`);
                
                this.m_emitter.emitBoolJump(exp.sinfo, testreg, trueblck, falseblck);
                this.m_emitter.setActiveBlock(trueblck);
                
                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(ExpressionTypeEnvironment.join(this.m_assembly, ...cflow.tenvs), exp.flow.conds[i].action, ttreg, infertype);
                
                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype]);

                this.m_emitter.setActiveBlock(falseblck);
                cenv = ExpressionTypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
        }

        if(hasfalseflow) {
            const ttreg = this.m_emitter.generateTmpRegister();
            const aenv = this.checkExpression(cenv, exp.flow.elseAction as Expression, ttreg, infertype);

            results.push(aenv);
            rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, aenv.getExpressionResult().valtype]);
        }

        this.raiseErrorIf(exp.sinfo, !results.some((eev) => eev.hasNormalFlow()), "No feasible path in this conditional expression");

        const fulltype = this.m_assembly.typeUpperBound(results.map((eev) => eev.getExpressionResult().valtype.flowtype));
        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, rcb[1], rcb[2], fulltype);
            this.m_emitter.emitRegisterStore(exp.sinfo, convreg, trgt, this.m_emitter.registerResolvedTypeReference(fulltype), undefined);

            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        
        return ExpressionTypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.updateResultExpression(fulltype, eev.getExpressionResult().valtype.flowtype)));
    }

    private checkSwitchExpression(env: ExpressionTypeEnvironment, exp: SwitchExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg, undefined, { refok: refok, orok: false });

        const doneblck = this.m_emitter.createNewBlock("Lswitchexp_done");
        const matchvar = `$switch_@${exp.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariableBinder(exp.sinfo, venv.pushLocalScope(), matchvar, ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), vreg);

        let hasfalseflow = true;
        let results: ExpressionTypeEnvironment[] = [];
        let rblocks: [string, MIRRegisterArgument, ValueType][] = [];
        for (let i = 0; i < exp.flow.length && hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}action`);

            const test = this.checkSwitchGuard(exp.sinfo, cenv, matchvar, exp.flow[i].check, nextlabel, actionlabel);

            if(test.tenv === undefined) {
                this.m_emitter.setActiveBlock(actionlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as ExpressionTypeEnvironment;
            }
            else if(test.fenv === undefined) {
                //go though action block and skip rest of generation
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(test.tenv, exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype]);

                this.m_emitter.setActiveBlock(nextlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                hasfalseflow = false;
            }
            else {
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(test.tenv, exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype]);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as ExpressionTypeEnvironment;
            }
        }

        if (hasfalseflow) {
            this.m_emitter.emitAbort(exp.sinfo, "exhaustive");
        }
        this.raiseErrorIf(exp.sinfo, !results.some((eev) => eev.hasNormalFlow()), "No feasible path in this conditional expression");

        const etype = this.m_assembly.typeUpperBound(results.map((eev) => eev.getExpressionResult().valtype.flowtype));
        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, rcb[1], rcb[2], etype);
            this.m_emitter.emitRegisterStore(exp.sinfo, convreg, trgt, this.m_emitter.registerResolvedTypeReference(etype), undefined);

            this.m_emitter.localLifetimeEnd(exp.sinfo, matchvar);
            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        
        return ExpressionTypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.popLocalScope().setUniformResultExpression(etype)));
    }

    private checkMatchExpression(env: ExpressionTypeEnvironment, exp: MatchExpression, trgt: MIRRegisterArgument, refok: boolean, infertype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg, undefined, { refok: refok, orok: false });
        const cvname = venv.getExpressionResult().expvar;

        const doneblck = this.m_emitter.createNewBlock("Lswitchexp_done");
        const matchvar = `$match_@${exp.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariableBinder(exp.sinfo, venv.pushLocalScope(), matchvar, ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), vreg);

        let hasfalseflow = true;
        let results: ExpressionTypeEnvironment[] = [];
        let rblocks: [string, MIRRegisterArgument, ValueType, string[]][] = [];
        for (let i = 0; i < exp.flow.length && hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchexp_${i}action`);

            const test = this.checkMatchGuard(exp.sinfo, i, cenv, matchvar, cvname, exp.flow[i].check, nextlabel, actionlabel);

            if(test.tenv === undefined) {
                this.m_emitter.setActiveBlock(actionlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as ExpressionTypeEnvironment;
            }
            else if(test.fenv === undefined) {
                //go though action block and skip rest of generation
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(test.tenv, exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype, test.newlive]);

                this.m_emitter.setActiveBlock(nextlabel);
                this.m_emitter.emitDeadBlock(exp.sinfo);

                hasfalseflow = false;
            }
            else {
                this.m_emitter.setActiveBlock(actionlabel);

                const ttreg = this.m_emitter.generateTmpRegister();
                const truestate = this.checkExpression(test.tenv, exp.flow[i].action, ttreg, infertype);

                results.push(truestate);
                rblocks.push([this.m_emitter.getActiveBlockName(), ttreg, truestate.getExpressionResult().valtype, test.newlive]);

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as ExpressionTypeEnvironment;
            }
        }

        if (hasfalseflow) {
            this.m_emitter.emitAbort(exp.sinfo, "exhaustive");
        }
        this.raiseErrorIf(exp.sinfo, !results.some((eev) => eev.hasNormalFlow()), "No feasible path in this conditional expression");

        const etype = this.m_assembly.typeUpperBound(results.map((eev) => eev.getExpressionResult().valtype.flowtype));
        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            const convreg = this.emitInlineConvertIfNeeded(exp.sinfo, rcb[1], rcb[2], etype);
            this.m_emitter.emitRegisterStore(exp.sinfo, convreg, trgt, this.m_emitter.registerResolvedTypeReference(etype), undefined);

            this.m_emitter.localLifetimeEnd(exp.sinfo, matchvar);
            for (let i = 0; i < rcb[3].length; ++i) {
                this.m_emitter.localLifetimeEnd(exp.sinfo, rcb[3][i]);
            }

            this.m_emitter.emitDirectJump(exp.sinfo, doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        
        return ExpressionTypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.popLocalScope().setUniformResultExpression(etype)));
    }

    private checkExpression(env: ExpressionTypeEnvironment, exp: Expression, infertype: ResolvedType | undefined, refok?: boolean): ExpressionTypeEnvironment {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression:
                return this.checkLiteralNoneExpression(env, exp as LiteralNoneExpression, trgt);
            case ExpressionTag.LiteralNothingExpression:
                return this.checkLiteralNothingExpression(env, exp as LiteralNothingExpression, trgt);
            case ExpressionTag.LiteralBoolExpression:
                return this.checkLiteralBoolExpression(env, exp as LiteralBoolExpression, trgt);
            case ExpressionTag.LiteralNumberinoExpression:
                return this.checkLiteralNumberinoExpression(env, exp as LiteralNumberinoExpression, trgt, infertype);
            case ExpressionTag.LiteralIntegralExpression:
                return this.checkLiteralIntegralExpression(env, exp as LiteralIntegralExpression, trgt);
            case ExpressionTag.LiteralFloatPointExpression:
                return this.checkLiteralFloatExpression(env, exp as LiteralFloatPointExpression, trgt);
            case ExpressionTag.LiteralRationalExpression:
                return this.checkLiteralRationalExpression(env, exp as LiteralRationalExpression, trgt);
            case ExpressionTag.LiteralStringExpression:
                return this.checkLiteralStringExpression(env, exp as LiteralStringExpression, trgt);
            case ExpressionTag.LiteralRegexExpression:
                return this.checkLiteralRegexExpression(env, exp as LiteralRegexExpression, trgt);
            case ExpressionTag.LiteralTypedStringExpression:
                return this.checkCreateTypedString(env, exp as LiteralTypedStringExpression, trgt);
            case ExpressionTag.LiteralTypedPrimitiveConstructorExpression:
                return this.checkTypedTypedNumericConstructor(env, exp as LiteralTypedPrimitiveConstructorExpression, trgt);
            case ExpressionTag.LiteralTypedStringConstructorExpression:
                return this.checkDataStringConstructor(env, exp as LiteralTypedStringConstructorExpression, trgt);
            case ExpressionTag.AccessNamespaceConstantExpression:
                return this.checkAccessNamespaceConstant(env, exp as AccessNamespaceConstantExpression, trgt);
            case ExpressionTag.AccessStaticFieldExpression:
                return this.checkAccessStaticField(env, exp as AccessStaticFieldExpression, trgt);
            case ExpressionTag.AccessVariableExpression:
                return this.checkAccessVariable(env, exp as AccessVariableExpression, trgt);
            case ExpressionTag.ConstructorPrimaryExpression:
                return this.checkConstructorPrimary(env, exp as ConstructorPrimaryExpression, trgt);
            case ExpressionTag.ConstructorPrimaryWithFactoryExpression:
                return this.checkConstructorPrimaryWithFactory(env, exp as ConstructorPrimaryWithFactoryExpression, trgt);
            case ExpressionTag.ConstructorTupleExpression:
                return this.checkTupleConstructor(env, exp as ConstructorTupleExpression, trgt, infertype);
            case ExpressionTag.ConstructorRecordExpression:
                return this.checkRecordConstructor(env, exp as ConstructorRecordExpression, trgt, infertype);
            case ExpressionTag.ConstructorEphemeralValueList:
                return this.checkConstructorEphemeralValueList(env, exp as ConstructorEphemeralValueList, trgt, infertype);
            case ExpressionTag.SpecialConstructorExpression:
                return this.checkSpecialConstructorExpression(env, exp as SpecialConstructorExpression, trgt, infertype);
            case ExpressionTag.LogicActionExpression:
                return this.checkLogicActionExpression(env, exp as LogicActionExpression, trgt);
            case ExpressionTag.MapEntryConstructorExpression:
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, trgt, infertype);
            case ExpressionTag.SelectExpression:
                return this.checkSelect(env, exp as SelectExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.SwitchExpression:
                return this.checkSwitchExpression(env, exp as SwitchExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.MatchExpression:
                return this.checkMatchExpression(env, exp as MatchExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.ExpOrExpression:
                return this.checkOrExpression(env, exp as ExpOrExpression, trgt, infertype, extraok || { refok: false, orok: false });
            case ExpressionTag.BlockStatementExpression:
                return this.checkBlockExpression(env, exp as BlockStatementExpression, infertype, trgt);
            case ExpressionTag.IfExpression:
                return this.checkIfExpression(env, exp as IfExpression, trgt, (extraok && extraok.refok) || false, infertype);
            case ExpressionTag.MatchExpression:
                return this.checkMatchExpression(env, exp as MatchExpression, trgt, (extraok && extraok.refok) || false, infertype);
            default: {
                let res: ExpressionTypeEnvironment[] = [];

                if (exp.tag === ExpressionTag.PCodeInvokeExpression) {
                    res = this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.CallNamespaceFunctionOrOperatorExpression) {
                    res = this.checkCallNamespaceFunctionOrOperatorExpression(env, exp as CallNamespaceFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.CallStaticFunctionOrOperatorExpression) {
                    res = this.checkCallStaticFunctionOrOperatorExpression(env, exp as CallStaticFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.IsTypeExpression) {
                    res = this.checkIsTypeExpressionMulti(env, exp as IsTypeExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.AsTypeExpression) {
                    res = this.checkAsTypeExpressionMulti(env, exp as AsTypeExpression, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.PostfixOpExpression) {
                    res = this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false, infertype);
                }
                else if (exp.tag === ExpressionTag.PrefixNotOpExpression) {
                    res = this.checkPrefixNotOp(env, exp as PrefixNotOp, trgt, (extraok && extraok.refok) || false);
                }
                else if (exp.tag === ExpressionTag.BinKeyExpression) {
                    const bke = exp as BinKeyExpression;
                    if(bke.op === "===") {
                        res = this.strongEQ(bke.sinfo, env, bke.lhs, bke.rhs, trgt);
                    }
                    else {
                        res = this.strongNEQ(bke.sinfo, env, bke.lhs, bke.rhs, trgt);
                    }
                }
                else {
                    assert(exp.tag === ExpressionTag.BinLogicExpression);
                    res = this.checkBinLogic(env, exp as BinLogicExpression, trgt, (extraok && extraok.refok) || false);
                }

                return ExpressionTypeEnvironment.join(this.m_assembly, ...res);
            }
        }
    }

    private checkExpressionMultiFlow(env: TypeEnvironment, exp: Expression, trgt: MIRRegisterArgument, infertype: ResolvedType | undefined, extraok?: { refok: boolean, orok: boolean }): TypeEnvironment[] {
        if (exp.tag === ExpressionTag.PCodeInvokeExpression) {
            return this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.CallNamespaceFunctionOrOperatorExpression) {
            return this.checkCallNamespaceFunctionOrOperatorExpression(env, exp as CallNamespaceFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.CallStaticFunctionOrOperatorExpression) {
            return this.checkCallStaticFunctionOrOperatorExpression(env, exp as CallStaticFunctionOrOperatorExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.IsTypeExpression) {
            return this.checkIsTypeExpressionMulti(env, exp as IsTypeExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.AsTypeExpression) {
            return this.checkAsTypeExpressionMulti(env, exp as AsTypeExpression, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.PostfixOpExpression) {
            return this.checkPostfixExpression(env, exp as PostfixOp, trgt, (extraok && extraok.refok) || false, infertype);
        }
        else if (exp.tag === ExpressionTag.PrefixNotOpExpression) {
            return this.checkPrefixNotOp(env, exp as PrefixNotOp, trgt, (extraok && extraok.refok) || false);
        }
        else if (exp.tag === ExpressionTag.BinKeyExpression) {
            const bke = exp as BinKeyExpression;
            if (bke.op === "===") {
                return this.strongEQ(bke.sinfo, env, bke.lhs, bke.rhs, trgt);
            }
            else {
                return this.strongNEQ(bke.sinfo, env, bke.lhs, bke.rhs, trgt);
            }
        }
        else if (exp.tag  === ExpressionTag.BinLogicExpression) {
            return this.checkBinLogic(env, exp as BinLogicExpression, trgt, (extraok && extraok.refok) || false);
        }
        else {
            return [this.checkExpression(env, exp, trgt, infertype, extraok)];
        }
    }

    private checkDeclareSingleVariableExplicit(sinfo: SourceInfo, env: TypeEnvironment, vname: string, isConst: boolean, decltype: TypeSignature, venv: { etype: ValueType, etreg: MIRRegisterArgument } | undefined): TypeEnvironment {
        this.raiseErrorIf(sinfo, env.isVarNameDefined(vname), "Cannot shadow previous definition");

        this.raiseErrorIf(sinfo, venv === undefined && isConst, "Must define const var at declaration site");
        this.raiseErrorIf(sinfo, venv === undefined && decltype instanceof AutoTypeSignature, "Must define auto typed var at declaration site");

        const vtype = (decltype instanceof AutoTypeSignature) ? (venv as { etype: ValueType, etreg: MIRRegisterArgument }).etype : ValueType.createUniform(this.resolveAndEnsureTypeOnly(sinfo, decltype, env.terms));
        this.raiseErrorIf(sinfo, venv !== undefined && !this.m_assembly.subtypeOf(venv.etype.flowtype, vtype.layout), "Expression is not of declared type");

        const mirvtype = this.m_emitter.registerResolvedTypeReference(vtype.layout);
        this.m_emitter.localLifetimeStart(sinfo, vname, mirvtype);

        if (venv !== undefined) {
            const convreg = this.emitInlineConvertIfNeeded(sinfo, venv.etreg, venv.etype, vtype.layout);
            this.m_emitter.emitRegisterStore(sinfo, convreg, new MIRRegisterArgument(vname), mirvtype, undefined);
        }

        return env.addVar(vname, isConst, vtype.layout, venv !== undefined, venv !== undefined ? venv.etype.flowtype : vtype.flowtype);
    }

    private checkDeclareSingleVariableBinder(sinfo: SourceInfo, env: TypeEnvironment, vname: string, vtype: ValueType, etreg: MIRRegisterArgument): TypeEnvironment {
        this.raiseErrorIf(sinfo, env.isVarNameDefined(vname), "Cannot shadow previous definition");

        const mirvtype = this.m_emitter.registerResolvedTypeReference(vtype.flowtype);
        this.m_emitter.localLifetimeStart(sinfo, vname, mirvtype);

        const convreg = this.emitInlineConvertIfNeeded(sinfo, etreg, vtype, vtype.flowtype);
        this.m_emitter.emitRegisterStore(sinfo, convreg, new MIRRegisterArgument(vname), mirvtype, undefined);

        return env.addVar(vname, true, vtype.flowtype, true, vtype.flowtype);
    }

    private checkVariableDeclarationStatement(env: TypeEnvironment, stmt: VariableDeclarationStatement): TypeEnvironment {
        const infertype = stmt.vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vtype, env.terms);

        const etreg = this.m_emitter.generateTmpRegister();
        const venv = stmt.exp !== undefined ? this.checkExpression(env, stmt.exp, etreg, infertype, { refok: true, orok: true }) : undefined;

        if(venv !== undefined) {
            this.raiseErrorIf(stmt.sinfo, venv.getExpressionResult().valtype.flowtype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store Ephemeral value lists in variables");
        }

        const vv = venv !== undefined ? { etype: venv.getExpressionResult().valtype, etreg: etreg } : undefined;
        return this.checkDeclareSingleVariableExplicit(stmt.sinfo, venv || env, stmt.name, stmt.isConst, stmt.vtype, vv);
    }

    private checkVariablePackDeclarationStatement(env: TypeEnvironment, stmt: VariablePackDeclarationStatement): TypeEnvironment {
        let cenv = env;
        if (stmt.exp === undefined) {
            for (let i = 0; i < stmt.vars.length; ++i) {
                cenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, undefined);
            }
        }
        else {
            if (stmt.exp.length === 1) {
                let infertypes = stmt.vars.map((vds) => vds.vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, vds.vtype, env.terms));
                let infertype = infertypes.includes(undefined) ? undefined : ResolvedType.createSingle(ResolvedEphemeralListType.create(infertypes as ResolvedType[]));

                const etreg = this.m_emitter.generateTmpRegister();
                cenv = this.checkExpression(env, stmt.exp[0], etreg, infertype, { refok: true, orok: true });
                const eetype = cenv.getExpressionResult().valtype.flowtype;

                this.raiseErrorIf(stmt.sinfo, eetype.options.length !== 1 || !(eetype.options[0] instanceof ResolvedEphemeralListType), "Expected Ephemeral List for multi assign");

                const elt = eetype.options[0] as ResolvedEphemeralListType;
                this.raiseErrorIf(stmt.sinfo, stmt.vars.length !== elt.types.length, "Missing initializers for variables");

                //check if all the assignments are conversion free -- if so we can do a multi-load
                const convertfree = stmt.vars.every((v, i) => {
                    if(v.vtype instanceof AutoTypeSignature) {
                        return true;
                    }

                    const decltype = this.resolveAndEnsureTypeOnly(stmt.sinfo, v.vtype, cenv.terms);
                    const exptype = elt.types[i];

                    return decltype.isSameType(exptype);
                });

                if(convertfree) {
                    this.raiseErrorIf(stmt.sinfo, stmt.vars.some((vv) => env.isVarNameDefined(vv.name), "Cannot shadow previous definition"));

                    let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
                    for (let i = 0; i < stmt.vars.length; ++i) {
                        const decltype = stmt.vars[i].vtype instanceof AutoTypeSignature ? elt.types[i] : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vars[i].vtype, env.terms);

                        const mirvtype = this.m_emitter.registerResolvedTypeReference(decltype);
                        this.m_emitter.localLifetimeStart(stmt.sinfo, stmt.vars[i].name, mirvtype);

                        trgts.push({ pos: i, into: new MIRRegisterArgument(stmt.vars[i].name), oftype: mirvtype });
                    }

                    this.m_emitter.emitMultiLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(eetype), trgts);

                    cenv = cenv.multiVarUpdate(stmt.vars.map((vv, i) => {
                            const decltype = vv.vtype instanceof AutoTypeSignature ? elt.types[i] : this.resolveAndEnsureTypeOnly(stmt.sinfo, vv.vtype, env.terms);
                            return [stmt.isConst, vv.name, decltype, decltype]
                        }), 
                        []
                    );
                }
                else {
                    for (let i = 0; i < stmt.vars.length; ++i) {
                        const tlreg = this.m_emitter.generateTmpRegister();
                        this.m_emitter.emitLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(elt.types[i]), i, this.m_emitter.registerResolvedTypeReference(eetype), tlreg);

                        cenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, cenv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, { etype: ValueType.createUniform(elt.types[i]), etreg: tlreg });
                    }
                }
            }
            else {
                this.raiseErrorIf(stmt.sinfo, stmt.vars.length !== stmt.exp.length, "Missing initializers for variables");

                for (let i = 0; i < stmt.vars.length; ++i) {
                    const infertype = stmt.vars[i].vtype instanceof AutoTypeSignature ? undefined : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vars[i].vtype, env.terms);

                    const etreg = this.m_emitter.generateTmpRegister();
                    const venv = this.checkExpression(env, stmt.exp[i], etreg, infertype);

                    cenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, venv, stmt.vars[i].name, stmt.isConst, stmt.vars[i].vtype, { etype: venv.getExpressionResult().valtype, etreg: etreg });
                }
            }
        }

        return cenv;
    }

    private checkAssignSingleVariable(sinfo: SourceInfo, env: TypeEnvironment, vname: string, etype: ValueType, etreg: MIRRegisterArgument): TypeEnvironment {
        const vinfo = env.lookupVar(vname);
        this.raiseErrorIf(sinfo, vinfo === null, "Variable was not previously defined");
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, "Variable defined as const");

        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(etype.flowtype, (vinfo as VarInfo).declaredType), "Assign value is not subtype of declared variable type");

        const convreg = this.emitInlineConvertIfNeeded(sinfo, etreg, etype, (vinfo as VarInfo).declaredType) as MIRRegisterArgument;
        this.m_emitter.emitRegisterStore(sinfo, convreg, new MIRRegisterArgument(vname), this.m_emitter.registerResolvedTypeReference((vinfo as VarInfo).declaredType), undefined);

        return env.setVar(vname, etype.flowtype);
    }

    private checkVariableAssignmentStatement(env: TypeEnvironment, stmt: VariableAssignmentStatement): TypeEnvironment {
        const vinfo = env.lookupVar(stmt.name);
        this.raiseErrorIf(stmt.sinfo, vinfo === undefined, "Variable was not previously defined");

        const infertype = (vinfo as VarInfo).declaredType;
        const etreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.exp, etreg, infertype, { refok: true, orok: true });
       
        if(venv !== undefined) {
            this.raiseErrorIf(stmt.sinfo, venv.getExpressionResult().valtype.flowtype.options.some((opt) => opt instanceof ResolvedEphemeralListType), "Cannot store Ephemeral value lists in variables");
        }

        return this.checkAssignSingleVariable(stmt.sinfo, venv, stmt.name, venv.getExpressionResult().valtype, etreg);
    }

    private checkVariablePackAssignmentStatement(env: TypeEnvironment, stmt: VariablePackAssignmentStatement): TypeEnvironment {
        let cenv = env;

        if (stmt.exp.length === 1) {
            let infertypes = stmt.names.map((vn) => env.lookupVar(vn));
            this.raiseErrorIf(stmt.sinfo, infertypes.includes(null), "Variable was not previously defined");
            let infertype = ResolvedType.createSingle(ResolvedEphemeralListType.create(infertypes.map((vi) => (vi as VarInfo).declaredType)));

            const etreg = this.m_emitter.generateTmpRegister();
            cenv = this.checkExpression(env, stmt.exp[0], etreg, infertype, { refok: true, orok: true });
            const eetype = cenv.getExpressionResult().valtype.flowtype;

            this.raiseErrorIf(stmt.sinfo, eetype.options.length !== 1 || !(eetype.options[0] instanceof ResolvedEphemeralListType), "Expected Ephemeral List for multi assign");

            const elt = eetype.options[0] as ResolvedEphemeralListType;
            this.raiseErrorIf(stmt.sinfo, stmt.names.length !== elt.types.length, "Missing initializers for variables");

            //check if all the assignments are conversion free -- if so we can do a multi-load
            const convertfree = stmt.names.every((v, i) => {
                const decltype = (env.lookupVar(v) as VarInfo).declaredType;
                const exptype = elt.types[i];

                return decltype.isSameType(exptype);
            });

            if (convertfree) {
                this.raiseErrorIf(stmt.sinfo, stmt.names.some((vv) => !env.isVarNameDefined(vv), "Variable was not previously defined"));
                this.raiseErrorIf(stmt.sinfo, stmt.names.some((vv) => (env.lookupVar(vv) as VarInfo).isConst, "Variable is const"));

                let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
                for (let i = 0; i < stmt.names.length; ++i) {
                    const decltype = (env.lookupVar(stmt.names[i]) as VarInfo).declaredType;
                    const mirvtype = this.m_emitter.registerResolvedTypeReference(decltype);

                    const vstore = new MIRRegisterArgument(stmt.names[i]);
                    trgts.push({ pos: i, into: vstore, oftype: mirvtype });
                }

                this.m_emitter.emitMultiLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(eetype), trgts);

                cenv = cenv.multiVarUpdate([], stmt.names.map((vv) => [vv, (env.lookupVar(vv) as VarInfo).declaredType]));
            }
            else {
                for (let i = 0; i < stmt.names.length; ++i) {
                    const tlreg = this.m_emitter.generateTmpRegister();
                    this.m_emitter.emitLoadFromEpehmeralList(stmt.sinfo, etreg, this.m_emitter.registerResolvedTypeReference(elt.types[i]), i, this.m_emitter.registerResolvedTypeReference(eetype), tlreg);

                    cenv = this.checkAssignSingleVariable(stmt.sinfo, cenv, stmt.names[i], ValueType.createUniform(elt.types[i]), etreg);
                }
            }
        }
        else {
            this.raiseErrorIf(stmt.sinfo, stmt.names.length !== stmt.exp.length, "Missing initializers for variables");

            for (let i = 0; i < stmt.names.length; ++i) {
                const vinfo = env.lookupVar(stmt.names[i]);
                this.raiseErrorIf(stmt.sinfo, vinfo === null, "Variable was not previously defined");

                const infertype = (vinfo as VarInfo).declaredType;

                const etreg = this.m_emitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.exp[i], etreg, infertype);

                cenv = this.checkAssignSingleVariable(stmt.sinfo, cenv, stmt.names[i], venv.getExpressionResult().valtype, etreg);
            }
        }

        return cenv;
    }

    private getTypeOfStructuredAssignForMatch(sinfo: SourceInfo, env: TypeEnvironment, assign: StructuredAssignment): ResolvedType {
        if(assign instanceof TupleStructuredAssignment) {
            this.raiseErrorIf(sinfo, assign.assigns.some((asg) => asg.assigntype instanceof AutoTypeSignature), "Must specify all entry types on Tuple match destructure");

            const ttypes = assign.assigns.map((asg) => this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms));
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(ttypes));
        }
        else if(assign instanceof RecordStructuredAssignment) {
            this.raiseErrorIf(sinfo, assign.assigns.some((asg) => asg[1].assigntype instanceof AutoTypeSignature), "Must specify all property types on Record match destructure");

            const entries = assign.assigns.map((asg) => {
                return { pname: asg[0], ptype: this.resolveAndEnsureTypeOnly(sinfo, asg[1].assigntype, env.terms) };
            });
            return ResolvedType.createSingle(ResolvedRecordAtomType.create(entries));
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof NominalStructuredAssignment), "Can only destructure match on Tuples/Records/Entity types");

            const nassign = assign as NominalStructuredAssignment;
            return this.resolveAndEnsureTypeOnly(sinfo, nassign.atype, env.terms);
        }
    }

    private getTypeOfStructuredAssignForInfer(sinfo: SourceInfo, env: TypeEnvironment, assign: StructuredAssignment): ResolvedType | undefined {
        if(assign instanceof TupleStructuredAssignment) {
            if(assign.assigns.some((asg) => asg.assigntype instanceof AutoTypeSignature)) {
                return undefined;
            }
            else {
                const ttypes = assign.assigns.map((asg) => this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms));
                return ResolvedType.createSingle(ResolvedTupleAtomType.create(ttypes));
            }
        }
        else if(assign instanceof RecordStructuredAssignment) {
            if(assign.assigns.some((asg) => asg[1].assigntype instanceof AutoTypeSignature)) {
                return undefined;
            }
            else {
                const entries = assign.assigns.map((asg) => {
                    return { pname: asg[0], ptype: this.resolveAndEnsureTypeOnly(sinfo, asg[1].assigntype, env.terms) };
                });
                return ResolvedType.createSingle(ResolvedRecordAtomType.create(entries));
            }
        }
        else if(assign instanceof ValueListStructuredAssignment) {
            if(assign.assigns.some((asg) => asg.assigntype instanceof AutoTypeSignature)) {
                return undefined;
            }
            else {
                const ttypes = assign.assigns.map((asg) => this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms));
                return ResolvedType.createSingle(ResolvedEphemeralListType.create(ttypes));
            }
        }
        else {
            assert(assign instanceof NominalStructuredAssignment);

            const nassign = assign as NominalStructuredAssignment;
            const ntype = this.resolveAndEnsureTypeOnly(sinfo, nassign.atype, env.terms);
            if(ntype.options.length !== 1) {
                return undefined;
            }

            const entityorconcept = (ntype.options[0] instanceof ResolvedEntityAtomType) || (ntype.options[0] instanceof ResolvedConceptAtomType);
            if(!entityorconcept) {
                return undefined
            }

            return ntype;
        }
    }

    private getTypeOfStructuredAssignForAssign(sinfo: SourceInfo, env: TypeEnvironment, assign: StructuredAssignment, rhsflow: ResolvedType): ResolvedType {
        if(assign instanceof TupleStructuredAssignment) {
            this.raiseErrorIf(sinfo, !rhsflow.isUniqueTupleTargetType(), "Expected unique tuple type to assign from");
            this.raiseErrorIf(sinfo, rhsflow.getUniqueTupleTargetType().types.length !== assign.assigns.length, "Tuple length does not match assignment");

            const ttypes = assign.assigns.map((asg, i) => !(asg.assigntype instanceof AutoTypeSignature) ? this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms) : rhsflow.getUniqueTupleTargetType().types[i]);
            return ResolvedType.createSingle(ResolvedTupleAtomType.create(ttypes));
        }
        else if(assign instanceof RecordStructuredAssignment) {
            this.raiseErrorIf(sinfo, !rhsflow.isUniqueRecordTargetType(), "Expected unique record type to assign from");
            this.raiseErrorIf(sinfo, rhsflow.getUniqueRecordTargetType().entries.length !== assign.assigns.length, "Record property counts do not match assignment");
            this.raiseErrorIf(sinfo, rhsflow.getUniqueRecordTargetType().entries.some((v) => assign.assigns.find((entry) => entry[0] === v.pname) === undefined), "Mismatched property name in assignment");

            const entries = assign.assigns.map((asg) => {
                const entrytype = !(asg[1].assigntype instanceof AutoTypeSignature) ? this.resolveAndEnsureTypeOnly(sinfo, asg[1].assigntype, env.terms) : (rhsflow.getUniqueRecordTargetType().entries.find((entry) => entry.pname === asg[0]) as {pname: string, ptype: ResolvedType}).ptype;
                return { pname: asg[0], ptype: entrytype };
            });
            return ResolvedType.createSingle(ResolvedRecordAtomType.create(entries));
        }
        else if(assign instanceof ValueListStructuredAssignment) {
            const ttypes = assign.assigns.map((asg) => this.resolveAndEnsureTypeOnly(sinfo, asg.assigntype, env.terms));
            return ResolvedType.createSingle(ResolvedEphemeralListType.create(ttypes));
        }
        else {
            assert(assign instanceof NominalStructuredAssignment);

            const nassign = assign as NominalStructuredAssignment;
            return this.resolveAndEnsureTypeOnly(sinfo, nassign.atype, env.terms);
        }
    }

    private generateStructuredAssignOperations(sinfo: SourceInfo, env: TypeEnvironment, assign: StructuredAssignment, arg: MIRRegisterArgument, arglayouttype: ResolvedType, argoftype: ResolvedType): TypeEnvironment {
        const elreg = this.m_emitter.generateTmpRegister();
        let eltypes: ResolvedType[] = [];
        let elatom: ResolvedEphemeralListType | undefined = undefined;
        let declaredvars: [boolean, string, ResolvedType, ResolvedType][] = [];

        if(assign instanceof TupleStructuredAssignment) {
            let rindecies: number[] = [];
            let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
            assign.assigns.forEach((ap, i) => {
                const aptype = argoftype.getUniqueTupleTargetType().types[i];
                if(ap instanceof VariableDeclarationStructuredAssignment) {
                    eltypes.push(aptype);
                    declaredvars.push([true, ap.vname, aptype, aptype]);
                    rindecies.push(i);
                    trgts.push({pos: trgts.length, into: new MIRRegisterArgument(ap.vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                }
            });

            elatom = ResolvedEphemeralListType.create(eltypes);
            this.m_emitter.emitTupleProjectToEphemeral(sinfo, arg, this.m_emitter.registerResolvedTypeReference(arglayouttype), this.m_emitter.registerResolvedTypeReference(argoftype), rindecies, !argoftype.isUniqueTupleTargetType(), elatom, elreg);
            this.m_emitter.emitMultiLoadFromEpehmeralList(sinfo, elreg, this.m_emitter.registerResolvedTypeReference(ResolvedType.createSingle(elatom)), trgts);

            return env.multiVarUpdate(declaredvars, []);
        }
        else if(assign instanceof RecordStructuredAssignment) {
            let pnames: string[] = [];
            let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
            assign.assigns.forEach((ap, i) => {
                const aptype = (argoftype.getUniqueRecordTargetType().entries.find((ee) => ee.pname === ap[0]) as {pname: string, ptype: ResolvedType}).ptype;
                if(ap[1] instanceof VariableDeclarationStructuredAssignment) {
                    eltypes.push(aptype);
                    declaredvars.push([true, ap[1].vname, aptype, aptype]);
                    pnames.push(ap[0]);
                    trgts.push({pos: trgts.length, into: new MIRRegisterArgument(ap[1].vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                }
            });

            elatom = ResolvedEphemeralListType.create(eltypes);
            this.m_emitter.emitRecordProjectToEphemeral(sinfo, arg, this.m_emitter.registerResolvedTypeReference(arglayouttype), this.m_emitter.registerResolvedTypeReference(argoftype), pnames, !argoftype.isUniqueRecordTargetType(), elatom, elreg);
            this.m_emitter.emitMultiLoadFromEpehmeralList(sinfo, elreg, this.m_emitter.registerResolvedTypeReference(ResolvedType.createSingle(elatom)), trgts);

            return env.multiVarUpdate(declaredvars, []);
        }
        else if(assign instanceof ValueListStructuredAssignment) {
            let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
            assign.assigns.forEach((ap, i) => {
                const aptype = (argoftype.options[0] as ResolvedEphemeralListType).types[i];
                if(ap instanceof VariableDeclarationStructuredAssignment) {
                    eltypes.push(aptype);
                    declaredvars.push([true, ap.vname, aptype, aptype]);
                    trgts.push({pos: trgts.length, into: new MIRRegisterArgument(ap.vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                }
            });

            this.m_emitter.emitMultiLoadFromEpehmeralList(sinfo, arg, this.m_emitter.registerResolvedTypeReference(arglayouttype), trgts);

            return env.multiVarUpdate(declaredvars, []);
        }
        else {
            assert(assign instanceof NominalStructuredAssignment);

            const nassign = assign as NominalStructuredAssignment;

            this.raiseErrorIf(sinfo, argoftype.options.length !== 1, "Must be unique concept or entity");
            this.raiseErrorIf(sinfo, !(argoftype.options[0] instanceof ResolvedEntityAtomType) && (argoftype.options[0] as ResolvedConceptAtomType).conceptTypes.length !== 1, "Must be unique concept or entity");

            const ootype = ((argoftype.options[0] instanceof ResolvedEntityAtomType) ? (argoftype.options[0] as ResolvedEntityAtomType).object : (argoftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].concept) as OOPTypeDecl;
            const oobinds = (argoftype.options[0] instanceof ResolvedEntityAtomType) ? (argoftype.options[0] as ResolvedEntityAtomType).binds : (argoftype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
            
            if (ootype.attributes.includes("__constructable")) {
                //check for constructable special case here
                this.raiseErrorIf(sinfo, nassign.assigns.length === 1, "Missing destructor variable");
                this.raiseErrorIf(sinfo, nassign.assigns[0][0] !== undefined, "Named destructors not allowed on primitive constructable types");

                const ap = nassign.assigns[0];
                const apv = new MIRRegisterArgument((ap[1] as VariableDeclarationStructuredAssignment).vname);

                const atype = (ootype.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;
                const ratype = this.resolveAndEnsureTypeOnly(sinfo, atype, oobinds);

                this.m_emitter.emitExtract(sinfo, this.m_emitter.registerResolvedTypeReference(argoftype), this.m_emitter.registerResolvedTypeReference(ratype), arg, apv)
                return env.addVar(apv.nameID, true, ratype, true, ratype);
            }
            else {
                this.raiseErrorIf(sinfo, ootype.attributes.includes("__internal"), "Cannot deconstruct primitive values");

                const allfields = this.m_assembly.getAllOOFieldsConstructors(ootype, oobinds);
                const selectfields = [...allfields.req, ...allfields.opt].map((fe) => fe[1]);

                let usenames = nassign.assigns.every((ap) => ap[0] !== undefined);
                let usepos = nassign.assigns.every((ap) => ap[0] === undefined);
                this.raiseErrorIf(sinfo, (usenames && usepos), "Cannot mix named and positional destructor vars -- may want to allow later though");

                //
                //TODO: need to do checks that we are not hitting private or hidden fields here unless our scope is otherwise ok
                //      also do same in get, project, update, etc.
                //

                let pnames: MIRFieldKey[] = [];
                let trgts: { pos: number, into: MIRRegisterArgument, oftype: MIRType }[] = [];
                if (usepos) {
                    nassign.assigns.forEach((ap, i) => {
                        if (ap[1] instanceof VariableDeclarationStructuredAssignment) {
                            const ffi = selectfields[i];
                            const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ffi[0], ffi[2]), ffi[1].name)
                            const aptype = this.resolveAndEnsureTypeOnly(sinfo, ffi[1].declaredType, ffi[2]);

                            eltypes.push(aptype);
                            declaredvars.push([true, ap[1].vname, aptype, aptype]);
                            pnames.push(fkey);
                            trgts.push({pos: trgts.length, into: new MIRRegisterArgument(ap[1].vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                        }
                    });
                }
                else {
                    nassign.assigns.forEach((ap, i) => {
                        if (ap[1] instanceof VariableDeclarationStructuredAssignment) {
                            const ffix = selectfields.find((ff) => ff[1].name === ap[0]);
                            this.raiseErrorIf(sinfo, ffix === undefined, "Could not match field with destructor variable");

                            const ffi = ffix as [OOPTypeDecl, MemberFieldDecl, Map<string, ResolvedType>];
                            const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ffi[0], ffi[2]), ffi[1].name)
                            const aptype = this.resolveAndEnsureTypeOnly(sinfo, ffi[1].declaredType, ffi[2]);

                            eltypes.push(aptype);
                            declaredvars.push([true, ap[1].vname, aptype, aptype]);
                            pnames.push(fkey);
                            trgts.push({pos: trgts.length, into: new MIRRegisterArgument(ap[1].vname), oftype: this.m_emitter.registerResolvedTypeReference(aptype)});
                        }
                    });
                }

                elatom = ResolvedEphemeralListType.create(eltypes);
                this.m_emitter.emitEntityProjectToEphemeral(sinfo, arg, this.m_emitter.registerResolvedTypeReference(arglayouttype), this.m_emitter.registerResolvedTypeReference(argoftype), pnames, !argoftype.isUniqueCallTargetType(), elatom, elreg);
                this.m_emitter.emitMultiLoadFromEpehmeralList(sinfo, elreg, this.m_emitter.registerResolvedTypeReference(ResolvedType.createSingle(elatom)), trgts);

                return env.multiVarUpdate(declaredvars, []);
            }
        }
    }

    private checkStructuredVariableAssignmentStatement(env: TypeEnvironment, stmt: StructuredVariableAssignmentStatement): TypeEnvironment {
        const inferassign = this.getTypeOfStructuredAssignForInfer(stmt.sinfo, env, stmt.assign);

        const expreg = this.m_emitter.generateTmpRegister();
        const eenv = this.checkExpression(env, stmt.exp, expreg, inferassign, { refok: true, orok: true });

        const ofassigntype = this.getTypeOfStructuredAssignForAssign(stmt.sinfo, env, stmt.assign, eenv.getExpressionResult().valtype.flowtype);
        this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(ofassigntype, eenv.getExpressionResult().valtype.flowtype), "Not sure what happened but types don't match here");

        return this.generateStructuredAssignOperations(stmt.sinfo, env, stmt.assign, expreg, eenv.getExpressionResult().valtype.layout, ofassigntype);
    }

    private checkIfElseStatement(env: TypeEnvironment, stmt: IfElseStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, stmt.flow.conds.length > 1 && stmt.flow.elseAction === undefined, "Must terminate elseifs with an else clause");

        const doneblck = this.m_emitter.createNewBlock("Lifstmt_done");

        let cenv = env;
        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        for (let i = 0; i < stmt.flow.conds.length && hasfalseflow; ++i) {
            const testreg = this.m_emitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, stmt.flow.conds[i].cond, testreg, undefined, i === 0 ? { refok: true, orok: false } : undefined);
            this.raiseErrorIf(stmt.sinfo, !test.every((eev) => this.m_assembly.subtypeOf(eev.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "If test expression must return a Bool");

            const cflow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
            
            if (cflow.tenvs.length === 0) {
                //can just keep generating tests in striaght line
                cenv = TypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
            else if (cflow.fenvs.length === 0) {
                //go though true block (without jump) and then skip else
                const trueblck = this.m_emitter.createNewBlock(`Lifstmt_${i}true`);
                this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), trueblck);
                this.m_emitter.setActiveBlock(trueblck);

                const truestate = this.checkStatement(TypeEnvironment.join(this.m_assembly, ...cflow.tenvs), stmt.flow.conds[i].action);
                if(truestate.hasNormalFlow()) {
                    this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), doneblck);
                }

                results.push(truestate);
                hasfalseflow = false;
            }
            else {
                const trueblck = this.m_emitter.createNewBlock(`Lifstmt_${i}true`);
                const falseblck = this.m_emitter.createNewBlock(`Lifstmt_${i}false`);
                
                this.m_emitter.emitBoolJump(SourceInfo.createIgnoreSourceInfo(), testreg, trueblck, falseblck);
                this.m_emitter.setActiveBlock(trueblck);
                
                const truestate = this.checkStatement(TypeEnvironment.join(this.m_assembly, ...cflow.tenvs), stmt.flow.conds[i].action);
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), doneblck);
                }
                
                this.m_emitter.setActiveBlock(falseblck);
                
                results.push(truestate);
                cenv = TypeEnvironment.join(this.m_assembly, ...cflow.fenvs);
            }
        }

        if (stmt.flow.elseAction === undefined || !hasfalseflow) {
            results.push(cenv);

            if(cenv.hasNormalFlow()) {
                this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), doneblck);
            }
        }
        else {
            const aenv = this.checkStatement(cenv, stmt.flow.elseAction);
            results.push(aenv);

            if (aenv.hasNormalFlow()) {
                this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), doneblck);
            }
        }

        this.m_emitter.setActiveBlock(doneblck);
        return TypeEnvironment.join(this.m_assembly, ...results);
    }

    private checkSwitchGuard(sinfo: SourceInfo, env: TypeEnvironment, switchvname: string, guard: SwitchGuard, nextlabel: string, actionlabel: string): { tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } {
        let opts: { tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } = { tenv: undefined, fenv: undefined };
        let mreg = this.m_emitter.generateTmpRegister();

        if (guard instanceof WildcardSwitchGuard) {
            this.m_emitter.emitLoadConstBool(sinfo, true, mreg);
            opts = { tenv: env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True), fenv: undefined };
        }
        else {
            const lguard = guard as LiteralSwitchGuard;

            const lexpx = this.m_assembly.reduceLiteralValueToCanonicalForm(lguard.litmatch.exp, env.terms, undefined);
            this.raiseErrorIf(sinfo, lexpx === undefined);

            const lexp = lexpx as [Expression, ResolvedType, string];
            const eqs = this.strongEQ(sinfo, env, lexp[0], new AccessVariableExpression(sinfo, switchvname), mreg);

            const fflows = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, eqs);
            opts = {
                tenv: fflows.tenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...fflows.tenvs) : undefined,
                fenv: fflows.fenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...fflows.fenvs) : undefined
            };
        }

        if(opts.tenv === undefined) {
            this.m_emitter.emitDirectJump(sinfo, nextlabel);
        }
        else if (opts.fenv === undefined) {
            this.m_emitter.emitDirectJump(sinfo, actionlabel);
        }
        else {
            this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
        }

        return opts;
    }

    private checkMatchGuard(sinfo: SourceInfo, midx: number, env: TypeEnvironment, matchvname: string, cvname: string | undefined, guard: MatchGuard, nextlabel: string, actionlabel: string): { newlive: string[], tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } {
        let opts: { tenv: TypeEnvironment | undefined, fenv: TypeEnvironment | undefined } = { tenv: undefined, fenv: undefined };
        let mreg = this.m_emitter.generateTmpRegister();

        const vspecial = new MIRRegisterArgument(matchvname);
        const vspecialinfo = env.getLocalVarInfo(matchvname) as VarInfo;
        env = env.setResultExpression(vspecialinfo.declaredType, vspecialinfo.flowType, undefined, undefined);

        let lifetimes: string[] = [];
        if (guard instanceof WildcardMatchGuard) {
            this.m_emitter.emitLoadConstBool(sinfo, true, mreg);
            opts = { tenv: env.setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True), fenv: undefined };

            this.m_emitter.emitDirectJump(sinfo, actionlabel);
        }
        else if (guard instanceof TypeMatchGuard) {
            const tmatch = this.resolveAndEnsureTypeOnly(sinfo, guard.oftype, env.terms);
            this.m_emitter.emitTypeOf(sinfo, mreg, this.m_emitter.registerResolvedTypeReference(tmatch), vspecial, this.m_emitter.registerResolvedTypeReference(vspecialinfo.declaredType), this.m_emitter.registerResolvedTypeReference(vspecialinfo.flowType), undefined);
            
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, tmatch, [env]);
            const okenvs = fflows.tenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
            const failenvs = fflows.fenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

            opts = {
                tenv: okenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...okenvs) : undefined,
                fenv: failenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...failenvs) : undefined
            };

            if (opts.tenv === undefined) {
                this.m_emitter.emitDirectJump(sinfo, nextlabel);
            }
            else if (opts.fenv === undefined) {
                this.m_emitter.emitDirectJump(sinfo, actionlabel);
            }
            else {
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
            }
        }
        else {
            const sguard = guard as StructureMatchGuard;

            const assigntype = this.getTypeOfStructuredAssignForMatch(sinfo, env, sguard.match);
            this.m_emitter.emitTypeOf(sinfo, mreg, this.m_emitter.registerResolvedTypeReference(assigntype), vspecial, this.m_emitter.registerResolvedTypeReference(vspecialinfo.declaredType), this.m_emitter.registerResolvedTypeReference(vspecialinfo.flowType), undefined);
            
            const fflows = TypeEnvironment.convertToTypeNotTypeFlowsOnResult(this.m_assembly, assigntype, [env]);
            const okenvs = fflows.tenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.True));
            const failenvs = fflows.fenvs.map((eev) => eev.inferVarsOfType(eev.getExpressionResult().valtype.flowtype, matchvname, cvname).setBoolResultExpression(this.m_assembly.getSpecialBoolType(), FlowTypeTruthValue.False));

            opts = {
                tenv: okenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...okenvs) : undefined,
                fenv: failenvs.length !== 0 ? TypeEnvironment.join(this.m_assembly, ...failenvs) : undefined
            };

            if (opts.tenv === undefined) {
                this.m_emitter.emitDirectJump(sinfo, nextlabel);
            }
            else if (opts.fenv === undefined) {
                this.m_emitter.emitDirectJump(sinfo, actionlabel);
            }
            else {
                this.m_emitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
            }

            if (opts.tenv !== undefined) {
                lifetimes = [...sguard.decls].sort();
                this.m_emitter.setActiveBlock(actionlabel);

                opts.tenv = this.generateStructuredAssignOperations(sinfo, opts.tenv, sguard.match, vspecial, vspecialinfo.declaredType, assigntype);
            }
        }

        return {
            newlive: lifetimes,
            tenv: opts.tenv,
            fenv: opts.fenv
        };
    }

    private checkSwitchStatement(env: TypeEnvironment, stmt: SwitchStatement): TypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.sval, vreg, undefined, { refok: true, orok: false });
        
        const doneblck = this.m_emitter.createNewBlock("Lswitchstmt_done");
        const matchvar = `$switch_@${stmt.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariableBinder(stmt.sinfo, venv.pushLocalScope(), matchvar, ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), vreg);

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: string[] = [];
        for (let i = 0; i < stmt.flow.length && hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}action`);

            const test = this.checkSwitchGuard(SourceInfo.createIgnoreSourceInfo(), cenv, matchvar, stmt.flow[i].check, nextlabel, actionlabel);

            if(test.tenv === undefined) {
                this.m_emitter.setActiveBlock(actionlabel);
                this.m_emitter.emitDeadBlock(SourceInfo.createIgnoreSourceInfo());

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as TypeEnvironment;
            }
            else if(test.fenv === undefined) {
                //go though action block and skip rest of generation
                this.m_emitter.setActiveBlock(actionlabel);

                const truestate = this.checkStatement(test.tenv, stmt.flow[i].action);

                results.push(truestate);
                if(truestate.hasNormalFlow()) {
                    rblocks.push(actionlabel);
                }

                this.m_emitter.setActiveBlock(nextlabel);
                this.m_emitter.emitDeadBlock(SourceInfo.createIgnoreSourceInfo());

                hasfalseflow = false;
            }
            else {
                this.m_emitter.setActiveBlock(actionlabel);

                const truestate = this.checkStatement(test.tenv, stmt.flow[i].action);

                results.push(truestate);
                if(truestate.hasNormalFlow()) {
                    rblocks.push(actionlabel);
                }

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as TypeEnvironment;
            }
        }

        if (hasfalseflow) {
            this.m_emitter.emitAbort(stmt.sinfo, "exhaustive");
        }

        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb);

            this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        if(results.length === 0) {
            this.m_emitter.emitAbort(stmt.sinfo, "Terminal Flows");
            return env.setAbort();
        }

        return TypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.popLocalScope()));
    }

    private checkMatchStatement(env: TypeEnvironment, stmt: MatchStatement): TypeEnvironment {
        const vreg = this.m_emitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.sval, vreg, undefined, { refok: true, orok: false });
        const cvname = venv.getExpressionResult().expvar;

        const doneblck = this.m_emitter.createNewBlock("Lswitchstmt_done");
        const matchvar = `$match_@${stmt.sinfo.pos}`;
        let cenv = this.checkDeclareSingleVariableBinder(stmt.sinfo, venv.pushLocalScope(), matchvar, ValueType.createUniform(venv.getExpressionResult().valtype.flowtype), vreg);

        let hasfalseflow = true;
        let results: TypeEnvironment[] = [];
        let rblocks: [string, string[]][] = [];
        for (let i = 0; i < stmt.flow.length && hasfalseflow; ++i) {
            const nextlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}next`);
            const actionlabel = this.m_emitter.createNewBlock(`Lswitchstmt_${i}action`);

            const test = this.checkMatchGuard(stmt.sinfo, i, cenv, matchvar, cvname, stmt.flow[i].check, nextlabel, actionlabel);

            if(test.tenv === undefined) {
                this.m_emitter.setActiveBlock(actionlabel);
                this.m_emitter.emitDeadBlock(SourceInfo.createIgnoreSourceInfo());

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as TypeEnvironment;
            }
            else if(test.fenv === undefined) {
                //go though action block and skip rest of generation
                this.m_emitter.setActiveBlock(actionlabel);

                const truestate = this.checkStatement(test.tenv, stmt.flow[i].action);

                results.push(truestate);
                if(truestate.hasNormalFlow()) {
                    rblocks.push([actionlabel, test.newlive]);
                }

                this.m_emitter.setActiveBlock(nextlabel);
                this.m_emitter.emitDeadBlock(SourceInfo.createIgnoreSourceInfo());

                hasfalseflow = false;
            }
            else {
                this.m_emitter.setActiveBlock(actionlabel);

                const truestate = this.checkStatement(test.tenv, stmt.flow[i].action);

                results.push(truestate);
                if(truestate.hasNormalFlow()) {
                    rblocks.push([actionlabel, test.newlive]);
                }

                this.m_emitter.setActiveBlock(nextlabel);
                cenv = test.fenv as TypeEnvironment;
            }
        }

        if (hasfalseflow) {
            this.m_emitter.emitAbort(stmt.sinfo, "exhaustive");
        }

        for (let i = 0; i < rblocks.length; ++i) {
            const rcb = rblocks[i];
            this.m_emitter.setActiveBlock(rcb[0]);

            this.m_emitter.localLifetimeEnd(SourceInfo.createIgnoreSourceInfo(), matchvar);
            for (let i = 0; i < rcb[1].length; ++i) {
                this.m_emitter.localLifetimeEnd(SourceInfo.createIgnoreSourceInfo(), rcb[1][i]);
            }

            this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), doneblck);
        }

        this.m_emitter.setActiveBlock(doneblck);
        if(results.length === 0) {
            this.m_emitter.emitAbort(stmt.sinfo, "Terminal Flows");
            return env.setAbort();
        }

        return TypeEnvironment.join(this.m_assembly, ...results.map((eev) => eev.popLocalScope()));
    }

    private checkNakedCallStatement(env: TypeEnvironment, stmt: NakedCallStatement): TypeEnvironment {
        const rdiscard = this.m_emitter.generateTmpRegister();

        if(stmt.call instanceof CallNamespaceFunctionOrOperatorExpression) {
            const cenv = this.checkCallNamespaceFunctionOrOperatorExpression(env, stmt.call as CallNamespaceFunctionOrOperatorExpression, rdiscard, true);
            return TypeEnvironment.join(this.m_assembly, ...cenv);
        }
        else { 
            const cenv = this.checkCallStaticFunctionOrOperatorExpression(env, stmt.call as CallStaticFunctionOrOperatorExpression, rdiscard, true);
            return TypeEnvironment.join(this.m_assembly, ...cenv);
        }
    }

    private checkReturnStatement(env: TypeEnvironment, stmt: ReturnStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");

        if (stmt.values.length === 1) {
            const etreg = this.m_emitter.generateTmpRegister();
            const venv = this.checkExpression(env, stmt.values[0], etreg, env.inferResult, { refok: true, orok: false });

            const etype = env.inferResult || venv.getExpressionResult().valtype.flowtype;
            this.m_emitter.emitReturnAssign(stmt.sinfo, this.emitInlineConvertIfNeeded(stmt.sinfo, etreg, venv.getExpressionResult().valtype, etype), this.m_emitter.registerResolvedTypeReference(etype));
            this.m_emitter.emitDirectJump(stmt.sinfo, "returnassign");

            return env.setReturn(this.m_assembly, etype);
        }
        else {
            let regs: MIRRegisterArgument[] = [];
            let rtypes: ResolvedType[] = [];
            const itype = env.inferResult !== undefined ? env.inferResult.tryGetInferrableValueListConstructorType() : undefined;
            for (let i = 0; i < stmt.values.length; ++i) {
                const einfer = itype !== undefined ? itype.types[i] : undefined;

                const etreg = this.m_emitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.values[i], etreg, einfer);

                const rrtype = einfer || venv.getExpressionResult().valtype.flowtype;
                regs.push(this.emitInlineConvertIfNeeded(stmt.sinfo, etreg, venv.getExpressionResult().valtype, rrtype));
                rtypes.push(rrtype);
            }

            const etype = ResolvedType.createSingle(ResolvedEphemeralListType.create(rtypes));

            const elreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitConstructorValueList(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(etype), regs, elreg);
                
            this.m_emitter.emitReturnAssign(stmt.sinfo, elreg, this.m_emitter.registerResolvedTypeReference(etype));
            this.m_emitter.emitDirectJump(stmt.sinfo, "returnassign");

            return env.setReturn(this.m_assembly, etype);
        }
    }

    private checkYieldStatement(env: TypeEnvironment, stmt: YieldStatement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, !env.isInYieldBlock(), "Cannot use yield statment outside expression blocks");

        const yinfo = this.m_emitter.getActiveYieldSet();
        const yinfer = env.inferYield[env.inferYield.length - 1];

        if (stmt.values.length === 1) {
            const ytrgt = this.m_emitter.generateTmpRegister();
            const venv = this.checkExpression(env, stmt.values[0], ytrgt, yinfer, { refok: true, orok: false });

            const ctype = yinfer || venv.getExpressionResult().valtype.flowtype;
            const yvv = venv.getExpressionResult().valtype.inferFlow(ctype);

            yinfo.push([this.m_emitter.getActiveBlockName(), ytrgt, yvv]);
            return env.setYield(this.m_assembly, ctype);
        }
        else {
            let regs: MIRRegisterArgument[] = [];
            let rtypes: ResolvedType[] = [];
            const itype = yinfer !== undefined ? yinfer.tryGetInferrableValueListConstructorType() : undefined;
            for (let i = 0; i < stmt.values.length; ++i) {
                const einfer = itype !== undefined ? itype.types[i] : undefined;

                const etreg = this.m_emitter.generateTmpRegister();
                const venv = this.checkExpression(env, stmt.values[i], etreg, einfer);

                const rrtype = einfer || venv.getExpressionResult().valtype.flowtype;
                regs.push(this.emitInlineConvertIfNeeded(stmt.sinfo, etreg, venv.getExpressionResult().valtype, rrtype));
                rtypes.push(rrtype);
            }

            const etype = ResolvedType.createSingle(ResolvedEphemeralListType.create(rtypes));

            const elreg = this.m_emitter.generateTmpRegister();
            this.m_emitter.emitConstructorValueList(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(etype), regs, elreg);

            yinfo.push([this.m_emitter.getActiveBlockName(), elreg, ValueType.createUniform(etype)]);
            return env.setYield(this.m_assembly, etype);
        }
    }

    private checkAbortStatement(env: TypeEnvironment, stmt: AbortStatement): TypeEnvironment {
        this.m_emitter.emitAbort(stmt.sinfo, "abort");

        return env.setAbort();
    }

    private checkAssertStatement(env: TypeEnvironment, stmt: AssertStatement): TypeEnvironment {
        const testreg = this.m_emitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg, undefined);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

        const flow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
        if(flow.fenvs.length === 0) {
            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs);
        }
        else if(flow.tenvs.length === 0) {
            this.m_emitter.emitAbort(stmt.sinfo, "always false assert");
            return env.setAbort();
        }
        else {
            if (isBuildLevelEnabled(stmt.level, this.m_buildLevel)) {
                this.m_emitter.emitAssertCheck(stmt.sinfo, "assert fail", testreg);
            }

            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs);
        }
    }

    private checkDebugStatement(env: TypeEnvironment, stmt: DebugStatement): TypeEnvironment {
        if (stmt.value === undefined) {
            if (this.m_buildLevel === "debug") {
                this.m_emitter.emitDebugBreak(stmt.sinfo);
            }
        }
        else {
            const vreg = this.m_emitter.generateTmpRegister();
            const venv = this.checkExpression(env, stmt.value, vreg, undefined);

            if (this.m_buildLevel !== "release") {
                this.m_emitter.emitDebugPrint(stmt.sinfo, this.emitInlineConvertIfNeeded(stmt.sinfo, vreg, venv.getExpressionResult().valtype, this.m_emitter.assembly.getSpecialAnyConceptType()));
            }
        }

        return env;
    }

    private checkValidateStatement(env: TypeEnvironment, stmt: ValidateStatement): TypeEnvironment {
        const testreg = this.m_emitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg, undefined);

        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().valtype.flowtype, this.m_assembly.getSpecialBoolType())), "Type of logic op must be Bool");

        const flow = TypeEnvironment.convertToBoolFlowsOnResult(this.m_assembly, test);
        this.raiseErrorIf(stmt.sinfo, env.inferResult !== undefined, "Cannot do type inference if using validate in the body");
        
        if(flow.fenvs.length === 0) {
            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs);
        }
        else {
            const rrtype = env.inferResult as ResolvedType;

            this.raiseErrorIf(stmt.sinfo, !rrtype.isResultType(), "Result must be an Result<T, E> type");
            const {T, E} = this.getTEBinds(this.getUniqueTypeBinds(rrtype));
            const errtype = this.m_assembly.getErrType(T, E);

            const doneblck = this.m_emitter.createNewBlock("Lcheck_done");
            const failblck = this.m_emitter.createNewBlock("Lcheck_fail");
            
            this.m_emitter.emitBoolJump(stmt.sinfo, testreg, doneblck, failblck);
            this.m_emitter.setActiveBlock(failblck);

            const errreg = this.m_emitter.generateTmpRegister();
            const errflow = TypeEnvironment.join(this.m_assembly, ...flow.fenvs.map((te) => te.setReturn(this.m_assembly, rrtype)));
           
            let errenv = errflow;
            if (stmt.err instanceof LiteralNoneExpression) {
                this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(E, this.m_assembly.getSpecialNoneType()));

                const ctarg = new MIRConstantNone();
                this.m_emitter.emitInject(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()), this.m_emitter.registerResolvedTypeReference(errtype), ctarg, errreg);
            }
            else {
                const terrreg = this.m_emitter.generateTmpRegister();
                const errevalenv = this.checkExpression(errflow, stmt.err, terrreg, rrtype);
                const errres = errevalenv.getExpressionResult().valtype;
                this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(E, rrtype), "Error result must evaluate to Result<T, E>");

                const ctarg = this.emitInlineConvertToFlow(stmt.sinfo, terrreg, errres);
                this.m_emitter.emitInject(stmt.sinfo, this.m_emitter.registerResolvedTypeReference(errres.flowtype), this.m_emitter.registerResolvedTypeReference(errtype), ctarg, errreg);
            }

            this.m_emitter.emitReturnAssign(stmt.sinfo, errreg, this.m_emitter.registerResolvedTypeReference(rrtype));
            this.m_emitter.emitDirectJump(stmt.sinfo, "returnassign");

            this.m_emitter.setActiveBlock(doneblck);

            errenv = errflow.setReturn(this.m_assembly, rrtype);
            return TypeEnvironment.join(this.m_assembly, ...flow.tenvs, errenv);
        }
    }

    private checkStatement(env: TypeEnvironment, stmt: Statement): TypeEnvironment {
        this.raiseErrorIf(stmt.sinfo, !env.hasNormalFlow(), "Unreachable statements");

        switch (stmt.tag) {
            case StatementTag.EmptyStatement:
                return env;
            case StatementTag.VariableDeclarationStatement:
                return this.checkVariableDeclarationStatement(env, stmt as VariableDeclarationStatement).clearExpressionResult();
            case StatementTag.VariablePackDeclarationStatement:
                return this.checkVariablePackDeclarationStatement(env, stmt as VariablePackDeclarationStatement).clearExpressionResult();
            case StatementTag.VariableAssignmentStatement:
                return this.checkVariableAssignmentStatement(env, stmt as VariableAssignmentStatement).clearExpressionResult();
            case StatementTag.VariablePackAssignmentStatement:
                return this.checkVariablePackAssignmentStatement(env, stmt as VariablePackAssignmentStatement).clearExpressionResult();
            case StatementTag.StructuredVariableAssignmentStatement:
                return this.checkStructuredVariableAssignmentStatement(env, stmt as StructuredVariableAssignmentStatement).clearExpressionResult();
            case StatementTag.IfElseStatement:
                return this.checkIfElseStatement(env, stmt as IfElseStatement).clearExpressionResult();
            case StatementTag.SwitchStatement:
                return this.checkSwitchStatement(env, stmt as SwitchStatement).clearExpressionResult();
            case StatementTag.MatchStatement:
                return this.checkMatchStatement(env, stmt as MatchStatement).clearExpressionResult();
            case StatementTag.NakedCallStatement:
                return this.checkNakedCallStatement(env, stmt as NakedCallStatement).clearExpressionResult();
            case StatementTag.ReturnStatement:
                return this.checkReturnStatement(env, stmt as ReturnStatement).clearExpressionResult();
            case StatementTag.YieldStatement:
                return this.checkYieldStatement(env, stmt as YieldStatement).clearExpressionResult();
            case StatementTag.AbortStatement:
                return this.checkAbortStatement(env, stmt as AbortStatement).clearExpressionResult();
            case StatementTag.AssertStatement:
                return this.checkAssertStatement(env, stmt as AssertStatement).clearExpressionResult();
            case StatementTag.DebugStatement:
                return this.checkDebugStatement(env, stmt as DebugStatement).clearExpressionResult();
            case StatementTag.ValidateStatement:
                return this.checkValidateStatement(env, stmt as ValidateStatement).clearExpressionResult();
            default:
                this.raiseErrorIf(stmt.sinfo, stmt.tag !== StatementTag.BlockStatement, "Unknown statement");
                return this.checkBlock(env, stmt as BlockStatement).clearExpressionResult();
        }
    }

    private checkBlock(env: TypeEnvironment, stmt: BlockStatement): TypeEnvironment {
        let cenv = env.pushLocalScope();

        for (let i = 0; i < stmt.statements.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }

            cenv = this.checkStatement(cenv, stmt.statements[i]);
        }

        if (cenv.hasNormalFlow()) {
            const deadvars = cenv.getCurrentFrameNames();
            for (let i = 0; i < deadvars.length; ++i) {
                this.m_emitter.localLifetimeEnd(stmt.sinfo, deadvars[i]);
            }
        }

        return cenv.popLocalScope();
    }

    private emitPrelogForRefParamsAndPostCond(sinfo: SourceInfo, env: TypeEnvironment, refparams: string[]): string[] {
        let rpnames: string[] = [];

        for(let i = 0; i < refparams.length; ++i) {
            rpnames.push(`$${refparams[i]}`);
            const rpt = (env.lookupVar(refparams[0]) as VarInfo).declaredType;
            this.m_emitter.emitRegisterStore(sinfo, new MIRRegisterArgument(refparams[i]), new MIRRegisterArgument(`$${refparams[i]}`), this.m_emitter.registerResolvedTypeReference(rpt), undefined);
        }

        return rpnames;
    }

    private emitPrologForReturn(sinfo: SourceInfo, rrinfo: { declresult: MIRType, runtimeresult: MIRType, elrcount: number, refargs: [string, MIRType][] }, wpost: boolean) {
        if(wpost) {
            this.m_emitter.emitRegisterStore(sinfo, new MIRRegisterArgument("$__ir_ret__"), new MIRRegisterArgument("$return"), rrinfo.declresult, undefined);
        }

        if(rrinfo.refargs.length === 0) {
            this.m_emitter.emitRegisterStore(sinfo, new MIRRegisterArgument("$__ir_ret__"), new MIRRegisterArgument("$$return"), rrinfo.declresult, undefined);
        }
        else {
            const rreg = this.m_emitter.generateTmpRegister();

            if(rrinfo.elrcount === -1) {
                let args = [new MIRRegisterArgument("$__ir_ret__"), ...rrinfo.refargs.map((rv) => new MIRRegisterArgument(rv[0]))];
                this.m_emitter.emitConstructorValueList(sinfo, rrinfo.runtimeresult, args, rreg);
            }
            else {
                let args: MIRArgument[] = [new MIRRegisterArgument("$__ir_ret__")];
                for(let i = 0; i < rrinfo.refargs.length; ++i) {
                    args.push(new MIRRegisterArgument(rrinfo.refargs[i][0]));
                }

                this.m_emitter.emitMIRPackExtend(sinfo, new MIRRegisterArgument("$__ir_ret__"), rrinfo.declresult, args, rrinfo.runtimeresult, rreg);
            }

            this.m_emitter.emitRegisterStore(sinfo, rreg, new MIRRegisterArgument("$$return"), rrinfo.runtimeresult, undefined);
        }
    }

    private checkBodyExpression(srcFile: string, env: TypeEnvironment, body: Expression, activeResultType: ResolvedType | undefined, outparaminfo: { pname: string, ptype: ResolvedType }[]): MIRBody | undefined {
        this.m_emitter.initializeBodyEmitter(activeResultType);

        for (let i = 0; i < outparaminfo.length; ++i) {
            const opi = outparaminfo[i];
            this.m_emitter.emitLoadUninitVariableValue(SourceInfo.createIgnoreSourceInfo(), this.m_emitter.registerResolvedTypeReference(opi.ptype), new MIRRegisterArgument(opi.pname));
        }

        const etreg = this.m_emitter.generateTmpRegister();
        const evalue = this.checkExpression(env, body, etreg, undefined);

        this.m_emitter.emitReturnAssign(SourceInfo.createIgnoreSourceInfo(), this.emitInlineConvertIfNeeded(SourceInfo.createIgnoreSourceInfo(), etreg, evalue.getExpressionResult().valtype, env.inferResult || evalue.getExpressionResult().valtype.flowtype), this.m_emitter.registerResolvedTypeReference(evalue.getExpressionResult().valtype.flowtype));
        this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(evalue.getExpressionResult().valtype.flowtype, []);
        this.emitPrologForReturn(SourceInfo.createIgnoreSourceInfo(), rrinfo, false);
        this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), "exit");

        return this.m_emitter.getBody(srcFile, body.sinfo);
    }

    private checkBodyStatement(srcFile: string, env: TypeEnvironment, body: BlockStatement, activeResultType: ResolvedType | undefined, optparaminfo: { pname: string, ptype: ResolvedType, maskidx: number, initaction: InitializerEvaluationAction }[], outparaminfo: { pname: string, defonentry: boolean, ptype: ResolvedType }[], preject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined, postject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined | undefined): MIRBody | undefined {
        this.m_emitter.initializeBodyEmitter(activeResultType);

        for (let i = 0; i < outparaminfo.length; ++i) {
            const opi = outparaminfo[i];
            if(!opi.defonentry) {
                env = env.addVar(opi.pname, false, opi.ptype, false, opi.ptype);
                this.m_emitter.emitLoadUninitVariableValue(SourceInfo.createIgnoreSourceInfo(), this.m_emitter.registerResolvedTypeReference(opi.ptype), new MIRRegisterArgument(opi.pname));
            }
        }

        let opidone: Set<string> = new Set<string>(["this"]);
        for (let i = 0; i < optparaminfo.length; ++i) {
            const opidx = optparaminfo.findIndex((opp) => !opidone.has(opp.pname) && opp.initaction.deps.every((dep) => opidone.has(dep)));
            const opi = optparaminfo[opidx];

            const iv = opi.initaction;
            const oftype = opi.ptype;
            const storevar = new MIRRegisterArgument(opi.pname);
            const guard = new MIRMaskGuard("@maskparam@", opidx, optparaminfo.length);
            if(iv instanceof InitializerEvaluationLiteralExpression) {
                const ttmp = this.m_emitter.generateTmpRegister();
                const oftt = this.checkExpression(env, iv.constexp, ttmp, oftype).getExpressionResult().valtype;

                this.m_emitter.emitRegisterStore(SourceInfo.createIgnoreSourceInfo(), storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", this.emitInlineConvertIfNeeded(iv.constexp.sinfo, ttmp, oftt, oftype)));
            }
            else if (iv instanceof InitializerEvaluationConstantLoad) {
                this.m_emitter.emitRegisterStore(SourceInfo.createIgnoreSourceInfo(), storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", new MIRGlobalVariable(iv.gkey, iv.shortgkey)));
            }
            else {
                const civ = iv as InitializerEvaluationCallAction;
                this.m_emitter.emitInvokeFixedFunctionWithGuard(SourceInfo.createIgnoreSourceInfo(), civ.ikey, civ.args, undefined, this.m_emitter.registerResolvedTypeReference(oftype), storevar, new MIRStatmentGuard(guard, "defaultontrue", storevar));
            }

            opidone.add(opi.pname);
        }

        if (preject !== undefined) {
            const preargs = preject[1].map((pn) => new MIRRegisterArgument(pn));
            for (let i = 0; i < preject[0].length; ++i) {
                const prechk = preject[0][i];

                const prereg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitInvokeFixedFunction(SourceInfo.createIgnoreSourceInfo(), prechk.ikey, preargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), prereg);
                this.m_emitter.emitAssertCheck(SourceInfo.createIgnoreSourceInfo(), "Fail pre-condition", prereg);
            }
        }

        let postrnames: string[] = [];
        if (postject !== undefined) {
            postrnames = this.emitPrelogForRefParamsAndPostCond(SourceInfo.createIgnoreSourceInfo(), env, outparaminfo.filter((op) => op.defonentry).map((op) => op.pname));
        }

        const renv = this.checkBlock(env, body);
        this.raiseErrorIf(body.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(renv.inferResult as ResolvedType, outparaminfo.map((op) => [op.pname, op.ptype]));
        this.emitPrologForReturn(SourceInfo.createIgnoreSourceInfo(), rrinfo, postject !== undefined);

        if (postject !== undefined) {
            const postargs = [...postject[1].map((pn) => new MIRRegisterArgument(pn)), ...postrnames.map((prn) => new MIRRegisterArgument(prn))];

            for (let i = 0; i < postject[0].length; ++i) {
                const postchk = postject[0][i];

                const postreg = this.m_emitter.generateTmpRegister();
                this.m_emitter.emitInvokeFixedFunction(SourceInfo.createIgnoreSourceInfo(), postchk.ikey, postargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), postreg);
                this.m_emitter.emitAssertCheck(SourceInfo.createIgnoreSourceInfo(), "Fail post-condition", postreg);
            }
        }

        this.m_emitter.emitDirectJump(SourceInfo.createIgnoreSourceInfo(), "exit");

        return this.m_emitter.getBody(srcFile, body.sinfo);
    }

    private abortIfTooManyErrors() {
        //if (this.m_errors.length > 20) {
        //    throw new Error("More than 20 errors ... halting type checker");
        //}

        //
        //TODO: when we don't emit bodies we return undefined from exp to body -- this can spread and result in undefined refs in some body positions
        //      for now just abort on first error and be done to prevent this
        //

        throw new Error("Halting on type error");
    }

    private getCapturedTypeInfoForFields(sinfo: SourceInfo, captured: Set<string>, allfieldstypes: Map<string, ResolvedType>): Map<string, ResolvedType> {
        let cci = new Map<string, ResolvedType>();
        captured.forEach((cp) => {
            this.raiseErrorIf(sinfo, !allfieldstypes.get(cp.slice(1)), `Unbound variable reference in field initializer "${cp}"`);

            cci.set(cp, allfieldstypes.get(cp.slice(1)) as ResolvedType);
        });

        return cci;
    }

    private processExpressionForFieldInitializer(containingType: OOPTypeDecl, decl: MemberFieldDecl, binds: Map<string, ResolvedType>, allfieldstypes: Map<string, ResolvedType>): InitializerEvaluationAction {
        const ddecltype = this.resolveAndEnsureTypeOnly(decl.sourceLocation, decl.declaredType, binds);
        const enclosingType = MIRKeyGenerator.generateTypeKey(this.resolveOOTypeFromDecls(containingType, binds));
        const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(containingType, binds), decl.name, binds, [], "initfield");
        const bodyid = this.generateBodyID(decl.sourceLocation, decl.srcFile, "initfield");

        try {
            const cexp = decl.value as ConstantExpressionValue;
            if (cexp.captured.size === 0) {
                const lexp = this.m_assembly.compileTimeReduceConstantExpression(cexp.exp, binds, ddecltype);
                if(lexp !== undefined) {
                    return new InitializerEvaluationLiteralExpression(lexp);
                }
                else {
                    const gkey = MIRKeyGenerator.generateGlobalKeyWType(this.resolveOOTypeFromDecls(containingType, binds), decl.name, "initfield");
                    if (!this.m_emitter.masm.constantDecls.has(gkey.keyid)) {
                        const idecl = this.processInvokeInfo_ExpressionIsolated(bodyid, decl.srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, decl.sourceLocation, ["static_initializer", "private"], ddecltype, binds);
                        this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                        const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
                        const mirglobal = new MIRConstantDecl(enclosingType, gkey.keyid, gkey.shortname, [], decl.sourceLocation, decl.srcFile, dtype.typeID, ikeyinfo.keyid);

                        this.m_emitter.masm.constantDecls.set(gkey.keyid, mirglobal);
                    }

                    return new InitializerEvaluationConstantLoad(gkey.keyid, gkey.shortname);
                }
            }
            else {
                if (!this.m_emitter.masm.invokeDecls.has(ikeyinfo.keyid)) {
                    const capturedtypes = this.getCapturedTypeInfoForFields(decl.sourceLocation, cexp.captured, allfieldstypes);
                    const fparams = [...cexp.captured].sort().map((cp) => {
                        return { name: cp, refKind: undefined, ptype: capturedtypes.get(cp) as ResolvedType };
                    });

                    const idecl = this.processInvokeInfo_ExpressionLimitedArgs(bodyid, decl.srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, decl.sourceLocation, ["dynamic_initializer", "private", ...decl.attributes], fparams, ddecltype, binds);
                    this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);
                }

                return new InitializerEvaluationCallAction(ikeyinfo.keyid, ikeyinfo.shortname, [...cexp.captured].sort().map((cp) => new MIRRegisterArgument(cp)));
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return new InitializerEvaluationCallAction(ikeyinfo.keyid, ikeyinfo.shortname, []);
        }
    }

    private processExpressionForOptParamDefault(srcFile: string, pname: string, ptype: ResolvedType, cexp: ConstantExpressionValue, binds: Map<string, ResolvedType>, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl): InitializerEvaluationAction {
        const bodyid = this.generateBodyID(cexp.exp.sinfo, srcFile, "pdefault");
        const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, pname, binds, [], "pdefault");

        try {
            if (cexp.captured.size === 0) {
                const lexp = this.m_assembly.compileTimeReduceConstantExpression(cexp.exp, binds, ptype);
                if (lexp !== undefined) {
                    return new InitializerEvaluationLiteralExpression(lexp);
                }
                else {
                    const gkey =  MIRKeyGenerator.generateGlobalKeyWNamespace(bodyid /*not ns but sure*/, pname, "pdefault");
                    const idecl = this.processInvokeInfo_ExpressionIsolated(bodyid, srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, cexp.exp.sinfo, ["static_initializer", "private"], ptype, binds);
                    this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                    const dtype = this.m_emitter.registerResolvedTypeReference(ptype);
                    const mirglobal = new MIRConstantDecl(undefined, gkey.keyid, gkey.shortname, [], cexp.exp.sinfo, srcFile, dtype.typeID, ikeyinfo.keyid);

                    this.m_emitter.masm.constantDecls.set(gkey.keyid, mirglobal);

                    return new InitializerEvaluationConstantLoad(gkey.keyid, gkey.shortname);
                }
            }
            else {
                const ppnames = [...cexp.captured].sort();
                const fparams = ppnames.map((cp) => {
                    let cptype: ResolvedType | undefined = undefined;

                    const cparam = invoke.params.find((ip) => ip.name === cp);
                    if (cparam !== undefined) {
                        cptype = this.resolveAndEnsureTypeOnly(cexp.exp.sinfo, cparam.type as TypeSignature, binds);
                    }

                    this.raiseErrorIf(cexp.exp.sinfo, cptype === undefined, "Unbound variable in initializer expression");
                    return { name: cp, refKind: undefined, ptype: cptype as ResolvedType };
                });

                const idecl = this.processInvokeInfo_ExpressionGeneral(bodyid, srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, cexp.exp.sinfo, ["dynamic_initializer", "private"], fparams, ptype, binds, new Map<string, PCode>(), []);
                this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                return new InitializerEvaluationCallAction(ikeyinfo.keyid, ikeyinfo.shortname, [...cexp.captured].sort().map((cp) => new MIRRegisterArgument(cp)));
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return new InitializerEvaluationCallAction(ikeyinfo.keyid, ikeyinfo.shortname, []);
        }
    }

    private processGenerateSpecialInvariantDirectFunction(exps: [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean][], allfieldstypes: Map<string, ResolvedType>): { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[] {
        try {
            const clauses = exps.map((cev, i) => {
                const ccname = cev[3] ? `invariant@${i}` : `validate@${i}`
                const bodyid = this.generateBodyID(cev[0].exp.sinfo, cev[1].srcFile, ccname);
                const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, ccname, cev[2], []);

                const capturedtypes = this.getCapturedTypeInfoForFields(cev[0].exp.sinfo, cev[0].captured, allfieldstypes);
                const fparams = [...cev[0].captured].sort().map((cp) => {
                    return { name: cp, refKind: undefined, ptype: capturedtypes.get(cp) as ResolvedType };
                });

                const idecl = this.processInvokeInfo_ExpressionLimitedArgs(bodyid, cev[1].srcFile, cev[0].exp, ikeyinfo.keyid, ikeyinfo.shortname, cev[1].sourceLocation, ["invariant_clause", "private"], fparams, this.m_assembly.getSpecialBoolType(), cev[2]);
                this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                return { ikey: ikeyinfo.keyid, sinfo: cev[0].exp.sinfo, srcFile: cev[1].srcFile, args: [...cev[0].captured].sort() };
            });

            return clauses;
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return [];
        }
    }

    private constructorIsSimple(tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): boolean {
        return !this.constructorHasInvariants(tdecl, binds) && !this.constructorHasOptionals(tdecl, binds);
    }

    private constructorHasInvariants(tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): boolean {
        return this.m_assembly.getAllInvariantProvidingTypes(tdecl, binds).some((ipt) => ipt[1].invariants.length !== 0);
    }

    private constructorHasOptionals(tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): boolean {
        const allfields = this.m_assembly.getAllOOFieldsLayout(tdecl, binds);
        return [...allfields].some((ff) => ff[1][1].value !== undefined);
    }

    private generateEntityInitializerFunctions(tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): {invariantclauses: { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[], validateclauses: { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[], optinits: InitializerEvaluationAction[] } {
        const allfields = this.m_assembly.getAllOOFieldsLayout(tdecl, binds);
        const allfieldstypes = new Map<string, ResolvedType>();
        allfields.forEach((v, k) => allfieldstypes.set(k, this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, v[1].declaredType, v[2])));
        const optfields = [...allfields].filter((ff) => ff[1][1].value !== undefined).map((af) => af[1]);

        const invs = ([] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean][]).concat(...
            this.m_assembly.getAllInvariantProvidingTypes(tdecl, binds).map((ipt) => 
            ipt[1].invariants
            .filter((inv) => isBuildLevelEnabled(inv.level, this.m_buildLevel))
            .map((inv) => [inv.exp, ipt[1], ipt[2], true] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean]))
        );
        const invariantclauses = this.processGenerateSpecialInvariantDirectFunction(invs, allfieldstypes);

        const valdts = ([] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean][]).concat(...
            this.m_assembly.getAllInvariantProvidingTypes(tdecl, binds).map((ipt) => 
            ipt[1].validates
            .map((inv) => [inv.exp, ipt[1], ipt[2], false] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean]))
        );
        const validateclauses = this.processGenerateSpecialInvariantDirectFunction([...invs, ...valdts], allfieldstypes);

        const optinits = optfields.map((opf) => {
            return this.processExpressionForFieldInitializer(opf[0], opf[1], opf[2], allfieldstypes);
        });

        return {invariantclauses: invariantclauses, validateclauses: validateclauses, optinits: optinits};
    }

    private generateDirectConstructor(bodyid: string, env: TypeEnvironment, conskey: MIRInvokeKey, conskeyshort: string, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>, clauses: { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[]) {
        const constype = this.resolveOOTypeFromDecls(tdecl, binds);

        const allfields = this.m_assembly.getAllOOFieldsLayout(tdecl, binds);
        const allfieldstypes = new Map<string, ResolvedType>();
        allfields.forEach((v, k) => allfieldstypes.set(k, this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, v[1].declaredType, v[2])));

        const fieldparams = this.m_assembly.getAllOOFieldsConstructors(tdecl, binds);

        this.m_emitter.initializeBodyEmitter(undefined);

        for (let i = 0; i < clauses.length; ++i) {
            const ttarg = this.m_emitter.generateTmpRegister();
            const chkargs = clauses[i].args.map((cv) => new MIRRegisterArgument(cv));
            this.m_emitter.emitInvokeFixedFunction(clauses[i].sinfo, clauses[i].ikey, chkargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), ttarg);
            this.m_emitter.emitAssertCheck(clauses[i].sinfo, `Failed invariant ${i} at line ${clauses[i].sinfo.line}`, ttarg);
        }

        let consargs: MIRArgument[] = [];
        allfields.forEach((v) => {
            consargs.push(new MIRRegisterArgument(`$${v[1].name}`));
        });

        this.m_emitter.emitReturnAssignOfCons(tdecl.sourceLocation, this.m_emitter.registerResolvedTypeReference(constype), consargs);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(constype, []);
        this.emitPrologForReturn(tdecl.sourceLocation, rrinfo, false);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "exit");

        let params: MIRFunctionParameter[] = [];
        [...fieldparams.req, ...fieldparams.opt].forEach((fpi) => {
            const ftype =  this.m_emitter.registerResolvedTypeReference(this.resolveAndEnsureTypeOnly(fpi[1][1].sourceLocation, fpi[1][1].declaredType, fpi[1][2]));
            params.push(new MIRFunctionParameter(`$${fpi[0]}`, ftype.typeID));
        });

        const consbody = this.m_emitter.getBody(tdecl.srcFile, tdecl.sourceLocation);
        if (consbody !== undefined) {
            const consinv = new MIRInvokeBodyDecl(this.m_emitter.registerResolvedTypeReference(constype).typeID, bodyid, conskey, conskeyshort, ["constructor", "private"], false, tdecl.sourceLocation, tdecl.sourceLocation, tdecl.srcFile, params, 0, this.m_emitter.registerResolvedTypeReference(constype).typeID, undefined, undefined, consbody);
            this.m_emitter.masm.invokeDecls.set(conskey, consinv);
        }
    }

    private generateInitConstructor(bodyid: string, env: TypeEnvironment, conskey: MIRInvokeKey, conskeyshort: string, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>, optinits: InitializerEvaluationAction[], directcons: MIRInvokeKey) {
        const constype = this.resolveOOTypeFromDecls(tdecl, binds);

        const allfields = this.m_assembly.getAllOOFieldsLayout(tdecl, binds);
        const allfieldstypes = new Map<string, ResolvedType>();
        allfields.forEach((v, k) => allfieldstypes.set(k, this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, v[1].declaredType, v[2])));

        const optfields = [...allfields].filter((ff) => ff[1][1].value !== undefined).map((af) => af[1]);
        const fieldparams = this.m_assembly.getAllOOFieldsConstructors(tdecl, binds);

        this.m_emitter.initializeBodyEmitter(undefined);

        let opidone: Set<string> = new Set<string>();
        for(let i = 0; i < optfields.length; ++i) {
            const opidx = optfields.findIndex((vv, idx) => !opidone.has(`$${vv[1].name}`) && optinits[idx].deps.every((dep) => opidone.has(dep)));
            const ofi = optfields[opidx];
            const iv = optinits[opidx];

            const oftype = this.resolveAndEnsureTypeOnly(ofi[1].sourceLocation, ofi[1].declaredType, ofi[2]);
            const storevar = new MIRRegisterArgument(`$${ofi[1].name}`);
            const guard = new MIRMaskGuard("@maskparam@", opidx, optfields.length);
            if(iv instanceof InitializerEvaluationLiteralExpression) {
                const ttmp = this.m_emitter.generateTmpRegister();
                const oftt = this.checkExpression(env, iv.constexp, ttmp, oftype).getExpressionResult().valtype;

                this.m_emitter.emitRegisterStore(ofi[1].sourceLocation, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", this.emitInlineConvertIfNeeded(ofi[1].sourceLocation, ttmp, oftt, oftype)));
            }
            else if (iv instanceof InitializerEvaluationConstantLoad) {
                this.m_emitter.emitRegisterStore(ofi[1].sourceLocation, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", new MIRGlobalVariable(iv.gkey, iv.shortgkey)));
            }
            else {
                const civ = iv as InitializerEvaluationCallAction;
                this.m_emitter.emitInvokeFixedFunctionWithGuard(ofi[1].sourceLocation, civ.ikey, civ.args, undefined, this.m_emitter.registerResolvedTypeReference(oftype), storevar, new MIRStatmentGuard(guard, "defaultontrue", storevar));
            }

            opidone.add(`$${ofi[1].name}`);
        }

        let consargs: MIRArgument[] = [];
        allfields.forEach((v) => {
            consargs.push(new MIRRegisterArgument(`$${v[1].name}`));
        });

        const constmp = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitInvokeFixedFunction(tdecl.sourceLocation, directcons, consargs, undefined, this.m_emitter.registerResolvedTypeReference(constype), constmp);

        this.m_emitter.emitReturnAssign(tdecl.sourceLocation, constmp, this.m_emitter.registerResolvedTypeReference(constype));
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(constype, []);
        this.emitPrologForReturn(tdecl.sourceLocation, rrinfo, false);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "exit");

        let params: MIRFunctionParameter[] = [];
        [...fieldparams.req, ...fieldparams.opt].forEach((fpi) => {
            const ftype =  this.m_emitter.registerResolvedTypeReference(this.resolveAndEnsureTypeOnly(fpi[1][1].sourceLocation, fpi[1][1].declaredType, fpi[1][2]));
            params.push(new MIRFunctionParameter(`$${fpi[0]}`, ftype.typeID));
        });

        const consbody = this.m_emitter.getBody(tdecl.srcFile, tdecl.sourceLocation);
        if (consbody !== undefined) {
            const consinv = new MIRInvokeBodyDecl(this.m_emitter.registerResolvedTypeReference(constype).typeID, bodyid, conskey, conskeyshort, ["constructor", "private"], false, tdecl.sourceLocation, tdecl.sourceLocation, tdecl.srcFile, params, optfields.length, this.m_emitter.registerResolvedTypeReference(constype).typeID, undefined, undefined, consbody);
            this.m_emitter.masm.invokeDecls.set(conskey, consinv);
        }
    }

    private generateInvariantCheck(bodyid: string, env: TypeEnvironment, invkey: MIRInvokeKey, invkeyshort: string, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>, initinfo: {clauses: { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[], optinits: InitializerEvaluationAction[] }) {
        const constype = this.resolveOOTypeFromDecls(tdecl, binds);

        const allfields = this.m_assembly.getAllOOFieldsLayout(tdecl, binds);
        const allfieldstypes = new Map<string, ResolvedType>();
        allfields.forEach((v, k) => allfieldstypes.set(k, this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, v[1].declaredType, v[2])));

        const optfields = [...allfields].filter((ff) => ff[1][1].value !== undefined).map((af) => af[1]);
        const fieldparams = this.m_assembly.getAllOOFieldsConstructors(tdecl, binds);

        this.m_emitter.initializeBodyEmitter(undefined);

        let opidone: Set<string> = new Set<string>();
        for(let i = 0; i < optfields.length; ++i) {
            const opidx = optfields.findIndex((vv, idx) => !opidone.has(`$${vv[1].name}`) && initinfo.optinits[idx].deps.every((dep) => opidone.has(dep)));
            const ofi = optfields[opidx];
            const iv = initinfo.optinits[opidx];

            const oftype = this.resolveAndEnsureTypeOnly(ofi[1].sourceLocation, ofi[1].declaredType, ofi[2]);
            const storevar = new MIRRegisterArgument(`$${ofi[1].name}`);
            const guard = new MIRMaskGuard("@maskparam@", opidx, optfields.length);
            if(iv instanceof InitializerEvaluationLiteralExpression) {
                const ttmp = this.m_emitter.generateTmpRegister();
                const oftt = this.checkExpression(env, iv.constexp, ttmp, oftype).getExpressionResult().valtype;

                this.m_emitter.emitRegisterStore(ofi[1].sourceLocation, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", this.emitInlineConvertIfNeeded(ofi[1].sourceLocation, ttmp, oftt, oftype)));
            }
            else if (iv instanceof InitializerEvaluationConstantLoad) {
                this.m_emitter.emitRegisterStore(ofi[1].sourceLocation, storevar, storevar, this.m_emitter.registerResolvedTypeReference(oftype), new MIRStatmentGuard(guard, "defaultonfalse", new MIRGlobalVariable(iv.gkey, iv.shortgkey)));
            }
            else {
                const civ = iv as InitializerEvaluationCallAction;
                this.m_emitter.emitInvokeFixedFunctionWithGuard(ofi[1].sourceLocation, civ.ikey, civ.args, undefined, this.m_emitter.registerResolvedTypeReference(oftype), storevar, new MIRStatmentGuard(guard, "defaultontrue", storevar));
            }

            opidone.add(`$${ofi[1].name}`);
        }

        let checkargs = initinfo.clauses.map((cl) => {
            const ttarg = this.m_emitter.generateTmpRegister();
            const chkargs = cl.args.map((cv) => new MIRRegisterArgument(cv));
            this.m_emitter.emitInvokeFixedFunction(cl.sinfo, cl.ikey, chkargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), ttarg);

            return ttarg;
        });

        const resarg = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitLogicAction(tdecl.sourceLocation, resarg, "/\\", checkargs);

        this.m_emitter.emitReturnAssign(tdecl.sourceLocation, resarg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()));
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(this.m_assembly.getSpecialBoolType(), []);
        this.emitPrologForReturn(tdecl.sourceLocation, rrinfo, false);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "exit");

        let params: MIRFunctionParameter[] = [];
        [...fieldparams.req, ...fieldparams.opt].forEach((fpi) => {
            const ftype =  this.m_emitter.registerResolvedTypeReference(this.resolveAndEnsureTypeOnly(fpi[1][1].sourceLocation, fpi[1][1].declaredType, fpi[1][2]));
            params.push(new MIRFunctionParameter(`$${fpi[0]}`, ftype.typeID));
        });

        const invbody = this.m_emitter.getBody(tdecl.srcFile, tdecl.sourceLocation);
        if (invbody !== undefined) {
            const consinv = new MIRInvokeBodyDecl(this.m_emitter.registerResolvedTypeReference(constype).typeID, bodyid, invkey, invkeyshort, ["invariant", "private"], false, tdecl.sourceLocation, tdecl.sourceLocation, tdecl.srcFile, params, optfields.length, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()).typeID, undefined, undefined, invbody);
            this.m_emitter.masm.invokeDecls.set(invkey, consinv);
        }
    }

    private generateInjectableEntityInitializerFunctions(tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>, oftype: ResolvedType): {invariantclauses: { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[], validateclauses: { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[]} {
        const implicitfield = new Map<string, ResolvedType>().set("value", oftype);

        const invs = ([] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean][]).concat(...
            this.m_assembly.getAllInvariantProvidingTypes(tdecl, binds).map((ipt) => 
            ipt[1].invariants
            .filter((inv) => isBuildLevelEnabled(inv.level, this.m_buildLevel))
            .map((inv) => [inv.exp, ipt[1], ipt[2], true] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean]))
        );
        const invariantclauses = this.processGenerateSpecialInvariantDirectFunction(invs, implicitfield);

        const valdts = ([] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean][]).concat(...
            this.m_assembly.getAllInvariantProvidingTypes(tdecl, binds).map((ipt) => 
            ipt[1].validates
            .map((inv) => [inv.exp, ipt[1], ipt[2], false] as [ConstantExpressionValue, OOPTypeDecl, Map<string, ResolvedType>, boolean]))
        );
        const validateclauses = this.processGenerateSpecialInvariantDirectFunction([...invs, ...valdts], implicitfield);

        return {invariantclauses: invariantclauses, validateclauses: validateclauses};
    }

    private generateInjectableConstructor(bodyid: string, conskey: MIRInvokeKey, conskeyshort: string, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>, oftype: ResolvedType, clauses: { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[]) {
        const constype = this.resolveOOTypeFromDecls(tdecl, binds);

        this.m_emitter.initializeBodyEmitter(undefined);

        for (let i = 0; i < clauses.length; ++i) {
            const ttarg = this.m_emitter.generateTmpRegister();
            const chkargs = clauses[i].args.map((cv) => new MIRRegisterArgument(cv));
            this.m_emitter.emitInvokeFixedFunction(clauses[i].sinfo, clauses[i].ikey, chkargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), ttarg);
            this.m_emitter.emitAssertCheck(clauses[i].sinfo, `Failed invariant ${i} at ${clauses[i].sinfo.line}`, ttarg);
        }
        
        const trgt = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitInject(tdecl.sourceLocation, this.m_emitter.registerResolvedTypeReference(oftype), this.m_emitter.registerResolvedTypeReference(constype), new MIRRegisterArgument("$value"), trgt);
        this.m_emitter.emitReturnAssign(tdecl.sourceLocation, trgt, this.m_emitter.registerResolvedTypeReference(constype));
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(constype, []);
        this.emitPrologForReturn(tdecl.sourceLocation, rrinfo, false);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "exit");

        const params: MIRFunctionParameter[] = [new MIRFunctionParameter("$value", constype.typeID)];
        const consbody = this.m_emitter.getBody(tdecl.srcFile, tdecl.sourceLocation);
        if (consbody !== undefined) {
            const consinv = new MIRInvokeBodyDecl(this.m_emitter.registerResolvedTypeReference(constype).typeID, bodyid, conskey, conskeyshort, ["constructor", "private"], false, tdecl.sourceLocation, tdecl.sourceLocation, tdecl.srcFile, params, 0, this.m_emitter.registerResolvedTypeReference(constype).typeID, undefined, undefined, consbody);
            this.m_emitter.masm.invokeDecls.set(conskey, consinv);
        }
    }

    private generateInjectableInvariant(bodyid: string, invkey: MIRInvokeKey, invkeyshort: string, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>, clauses: { ikey: string, sinfo: SourceInfo, srcFile: string, args: string[] }[]) {
        const constype = this.resolveOOTypeFromDecls(tdecl, binds);

        this.m_emitter.initializeBodyEmitter(undefined);

        let checkargs = clauses.map((cl) => {
            const ttarg = this.m_emitter.generateTmpRegister();
            const chkargs = cl.args.map((cv) => new MIRRegisterArgument(cv));
            this.m_emitter.emitInvokeFixedFunction(cl.sinfo, cl.ikey, chkargs, undefined, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()), ttarg);

            return ttarg;
        });

        const resarg = this.m_emitter.generateTmpRegister();
        this.m_emitter.emitLogicAction(tdecl.sourceLocation, resarg, "/\\", checkargs);

        this.m_emitter.emitReturnAssign(tdecl.sourceLocation, resarg, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()));
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "returnassign");

        this.m_emitter.setActiveBlock("returnassign");

        const rrinfo = this.generateRefInfoForReturnEmit(this.m_assembly.getSpecialBoolType(), []);
        this.emitPrologForReturn(tdecl.sourceLocation, rrinfo, false);
        this.m_emitter.emitDirectJump(tdecl.sourceLocation, "exit");

        const params: MIRFunctionParameter[] = [new MIRFunctionParameter("$value", constype.typeID)];
        const invbody = this.m_emitter.getBody(tdecl.srcFile, tdecl.sourceLocation);
        if (invbody !== undefined) {
            const consinv = new MIRInvokeBodyDecl(this.m_emitter.registerResolvedTypeReference(constype).typeID, bodyid, invkey, invkeyshort, ["invariant", "private"], false, tdecl.sourceLocation, tdecl.sourceLocation, tdecl.srcFile, params, 0, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialBoolType()).typeID, undefined, undefined, invbody);
            this.m_emitter.masm.invokeDecls.set(invkey, consinv);
        }
    }

    private processGenerateSpecialPreFunction_FailFast(invkparams: {name: string, ptype: ResolvedType}[], pcodes: Map<string, PCode>, pargs: [string, ResolvedType][], exps: PreConditionDecl[], binds: Map<string, ResolvedType>, srcFile: string): { ikey: string, sinfo: SourceInfo, srcFile: string }[] {
        try {
            const clauses = exps
            .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
            .map((cev, i) => {
                const bodyid = this.generateBodyID(cev.sinfo, srcFile, `pre@${i}`);
                const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, `pre@${i}`, binds, []);

                const idecl = this.processInvokeInfo_ExpressionGeneral(bodyid, srcFile, cev.exp, ikeyinfo.keyid, ikeyinfo.shortname, cev.sinfo, ["precondition", "private"], invkparams, this.m_assembly.getSpecialBoolType(), binds, pcodes, pargs);
                this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                return { ikey: ikeyinfo.keyid, sinfo: cev.sinfo, srcFile: srcFile };
            });

            return clauses;
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return [];
        }
    }

    private processGenerateSpecialPreFunction_ResultT(sinfo: SourceInfo, exps: PreConditionDecl[], body: BodyImplementation): BodyImplementation {
        const ops = exps.map((pc) => {
            return new CondBranchEntry<BlockStatement>(new PrefixNotOp(pc.sinfo, pc.exp), new BlockStatement((pc.err as Expression).sinfo, [new ReturnStatement((pc.err as Expression).sinfo, [pc.err as Expression])]));
        });
        const ite = new IfElseStatement(sinfo, new IfElse<BlockStatement>(ops, body.body as BlockStatement));

        return new BodyImplementation(body.id, body.file, new BlockStatement(sinfo, [ite]));
    }

    private processGenerateSpecialPostFunction(invkparams: {name: string, ptype: ResolvedType}[], pcodes: Map<string, PCode>, pargs: [string, ResolvedType][], exps: PostConditionDecl[], binds: Map<string, ResolvedType>, srcFile: string): { ikey: string, sinfo: SourceInfo, srcFile: string }[] {
        try {
            const clauses = exps
            .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
            .map((cev, i) => {
                const bodyid = this.generateBodyID(cev.sinfo, srcFile, `post@${i}`);
                const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, `post@${i}`, binds, []);

                const idecl = this.processInvokeInfo_ExpressionGeneral(bodyid, srcFile, cev.exp, ikeyinfo.keyid, ikeyinfo.shortname, cev.sinfo, ["postcondition", "private"], invkparams, this.m_assembly.getSpecialBoolType(), binds, pcodes, pargs);
                this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

                return { ikey: ikeyinfo.keyid, sinfo: cev.sinfo, srcFile: srcFile };
            });

            return clauses;
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();

            return [];
        }
    }

/*

    private toTIRInvariantConsEntity(ttype: ResolvedType, invdecls: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][], allfields: TIRMemberFieldDecl[]): {invk: TIRInvokeKey, args: {fkey: TIRFieldKey, argidx: number, ftype: TIRTypeKey}[]}[] {
        const fargs = allfields.map((ff, idx) => {
            return {fkey: ff.fkey, argidx: idx, ftype: ff.declaredType};
        });

        const chkinvsaa = invdecls.map((idp) => {
            let invs = (idp[1].invariants.map((ii, iidx) => [ii, iidx]) as [InvariantDecl, number][]).filter((ie) => isBuildLevelEnabled(ie[0].level, this.m_buildLevel));
            return invs.map((inv) => {
                const invk = TIRInvokeIDGenerator.generateInvokeIDForInvariant(idp[0].typeID, inv[1]);
                const invtype = this.m_tirTypeMap.get(idp[0].typeID) as TIROOType;

                const args = fargs.filter((farg) => invtype.allfields.some((mf) => mf.fkey === farg.fkey));
                return {invk: invk, args: args};
            });
        });
        
        return ([] as {invk: TIRInvokeKey, args: {fkey: TIRFieldKey, argidx: number, ftype: TIRTypeKey}[]}[]).concat(...chkinvsaa);
    }

    private toTIRValidateConsEntity(ttype: ResolvedType, invdecls: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][], allfields: TIRMemberFieldDecl[]): {invk: TIRInvokeKey, args: {fkey: TIRFieldKey, argidx: number, ftype: TIRTypeKey}[]}[] {
        const fargs = allfields.map((ff, idx) => {
            return {fkey: ff.fkey, argidx: idx, ftype: ff.declaredType};
        });

        const chkinvsaa = invdecls.map((idp) => {
            let invs = (idp[1].validates.map((ii, iidx) => [ii, iidx]) as [ValidateDecl, number][]);
            return invs.map((inv) => {
                const invk = TIRInvokeIDGenerator.generateInvokeIDForValidate(idp[0].typeID, inv[1]);
                const invtype = this.m_tirTypeMap.get(idp[0].typeID) as TIROOType;

                const args = fargs.filter((farg) => invtype.allfields.some((mf) => mf.fkey === farg.fkey));
                return {invk: invk, args: args};
            });
        });
        
        return ([] as {invk: TIRInvokeKey, args: {fkey: TIRFieldKey, argidx: number, ftype: TIRTypeKey}[]}[]).concat(...chkinvsaa);
    }

    private toTIRInvariantConsTypedecl(ttype: ResolvedType, invdecls: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): [{invk: TIRInvokeKey, vtype: TIRTypeKey}[], {invk: TIRInvokeKey, vtype: TIRTypeKey}[]] {
       const chkinvsaa = invdecls.map((idp) => {
            let invs = (idp[1].invariants.map((ii, iidx) => [ii, iidx]) as [InvariantDecl, number][]).filter((ie) => isBuildLevelEnabled(ie[0].level, this.m_buildLevel));
            return invs.map((inv) => {
                const invk = TIRInvokeIDGenerator.generateInvokeIDForInvariant(idp[0].typeID, inv[1]);
                const invtype = this.m_tirTypeMap.get(idp[0].typeID) as TIRTypedeclEntityType;

                return {invk: invk, vtype: invtype.valuetype};
            });
        });

        const tinv = ((invdecls.find((idp) => idp[0].typeID === ttype.typeID) as [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>])[1].invariants.map((ii, iidx) => [ii, iidx]) as [InvariantDecl, number][]).filter((ie) => isBuildLevelEnabled(ie[0].level, this.m_buildLevel));
        const dinvs = tinv.map((inv) => {
            const invk = TIRInvokeIDGenerator.generateInvokeIDForInvariant(ttype.typeID, inv[1]);
            const invtype = this.m_tirTypeMap.get(ttype.typeID) as TIRTypedeclEntityType;

            return {invk: invk, vtype: invtype.valuetype};
        });

        return [([] as {invk: TIRInvokeKey, vtype: TIRTypeKey}[]).concat(...chkinvsaa), dinvs];
    }

    private toTIRValidateConsTypedecl(ttype: ResolvedType, invdecls: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): {invk: TIRInvokeKey, vtype: TIRTypeKey}[] {
        const chkinvsaa = invdecls.map((idp) => {
            let invs = (idp[1].validates.map((ii, iidx) => [ii, iidx]) as [InvariantDecl, number][]);
            return invs.map((inv) => {
                const invk = TIRInvokeIDGenerator.generateInvokeIDForValidate(idp[0].typeID, inv[1]);
                const invtype = this.m_tirTypeMap.get(idp[0].typeID) as TIRTypedeclEntityType;

                return {invk: invk, vtype: invtype.valuetype};
            });
        });

        return ([] as {invk: TIRInvokeKey, vtype: TIRTypeKey}[]).concat(...chkinvsaa);
    }

    private toTIRTypedeclChecks(ttype: ResolvedType, invdecls: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>][]): { strof: ResolvedType | undefined, pthof: {validator: ResolvedType, kind: "path" | "pathfragment" | "pathglob"} | undefined } {
        const chkvalidxx = invdecls.find((idp) => {
            return idp[1].attributes.includes("__stringof_type") || idp[1].attributes.includes("__asciistringof_type");
        });
        const chkvalid = (chkvalidxx !== undefined) ? (chkvalidxx[2].get("T") as ResolvedType) : undefined;

        const chkpathxx = invdecls.find((idp) => {
            return idp[1].attributes.includes("__path_type") || idp[1].attributes.includes("__pathfragment_type") || idp[1].attributes.includes("__pathglob_type");
        });
        const chkpath = (chkpathxx !== undefined) ? {validator: (chkpathxx[2].get("T") as ResolvedType), kind: (chkpathxx[1].attributes.includes("__path_type") ? "path" : (chkpathxx[1].attributes.includes("__pathfragment_type") ? "pathfragment" : "pathglob")) as "path" | "pathfragment" | "pathglob"} : undefined;

        return { strof: chkvalid, pthof: chkpath };
    }

    private toTIRMemberFields(encltypeid: string, enclname: TIRTypeName, fields: MemberFieldDecl[], binds: TemplateBindScope): TIRMemberFieldDecl[] {
        return fields.map((mf) => {
            const fkey = TIRMemberIDGenerator.generateMemberFieldID(encltypeid, mf.name);
            const fname = new TIRTypeMemberName(enclname, mf.name, undefined);
            const declaredtype = this.toTIRTypeKey(this.normalizeTypeOnly(mf.declaredType, binds));

            return new TIRMemberFieldDecl(fkey, fname, mf.name, encltypeid, mf.sourceLocation, mf.srcFile, mf.attributes, declaredtype);
        });
    }

    private toTIRAllFields(ttype: ResolvedType, ooptype: OOPTypeDecl, oobinds: Map<string, ResolvedType>): TIRMemberFieldDecl[] {
        const alldecls = this.getAllOOFields(ttype, ooptype, oobinds);
        return [...alldecls].map((entry) => (this.m_tirTypeMap.get(entry[1][0].typeID) as TIROOType).memberFields.find((mf) => mf.name === entry[0]) as TIRMemberFieldDecl);
    }
*/

    processOOType(tkey: MIRResolvedTypeKey, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        try {
            this.m_file = tdecl.srcFile;

            let terms = new Map<string, MIRType>();
            tdecl.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

            const provides = this.m_assembly.resolveProvides(tdecl, binds).map((provide) => {
                const ptype = this.resolveAndEnsureTypeOnly(new SourceInfo(0, 0, 0, 0), provide, binds);
                return this.m_emitter.registerResolvedTypeReference(ptype).typeID;
            });

            if (tdecl instanceof EntityTypeDecl) {
                if(tdecl.attributes.includes("__enum_type")) {
                    const enums = tdecl.staticMembers.map((sdecl) => sdecl.name);

                    const mirentity = new MIREnumEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, enums);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__typedprimitive")) {
                    const rrtype = (tdecl.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;
                    let oftype = this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, rrtype, binds);

                    let basetype = oftype;
                    let basetypedecl = basetype.getUniqueCallTargetType().object;
                    while(!basetypedecl.attributes.includes("__typebase")) {
                        const uutype = (basetypedecl.memberMethods.find((mm) => mm.name === "value") as MemberMethodDecl).invoke.resultType;

                        basetype = this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, uutype, basetype.getUniqueCallTargetType().binds);
                        basetypedecl = basetype.getUniqueCallTargetType().object;
                    }

                    let validatekey: string | undefined = undefined;
                    let conskey: string | undefined = undefined;
                    if(tdecl.invariants.length !== 0 || tdecl.validates.length !== 0) {
                        const initinfo = this.generateInjectableEntityInitializerFunctions(tdecl, binds, oftype);

                        const validatebodyid = this.generateBodyID(tdecl.sourceLocation, tdecl.srcFile, "@@validateinput");
                        const validatekeyid = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(tdecl, binds), "@@validateinput", new Map<string, ResolvedType>(), []);
                        this.generateInjectableInvariant(validatebodyid, validatekeyid.keyid, validatekeyid.shortname, tdecl, binds, initinfo.validateclauses);
                        validatekey = validatekeyid.keyid;

                        if (tdecl.invariants.length !== 0) {
                            const consbodyid = this.generateBodyID(tdecl.sourceLocation, tdecl.srcFile, "@@directconstructor");
                            const conskeyid = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(tdecl, binds), "@@directconstructor", new Map<string, ResolvedType>(), []);
                            this.generateInjectableConstructor(consbodyid, conskeyid.keyid, conskeyid.shortname, tdecl, binds, oftype, initinfo.invariantclauses);
                            conskey = conskeyid.keyid;
                        }
                    }
                    
                    const mirentity = new MIRConstructableEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, oftype.typeID, validatekey, conskey, basetype.typeID);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__stringof_type") || tdecl.attributes.includes("__datastring_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);
                    
                    if (tdecl.attributes.includes("__stringof_type")) {
                        const mirentity = new MIRStringOfInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID);
                        this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                    }
                    else {
                        const aoftype = (binds.get("T") as ResolvedType).options[0];
                        const oodecl = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.object : (aoftype as ResolvedConceptAtomType).conceptTypes[0].concept;
                        const oobinds = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.binds : (aoftype as ResolvedConceptAtomType).conceptTypes[0].binds;

                        const sf = (oodecl.staticFunctions.find((sfv) => sfv.name === "accepts") as StaticFunctionDecl);
                        const mirencltype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(oodecl, oobinds));
                        const accepts = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(oodecl, oobinds), [mirencltype, oodecl, oobinds], sf, "accepts", oobinds, [], []);

                        const mirentity = new MIRDataStringInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, accepts);
                        this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                    }
                }
                else if(tdecl.attributes.includes("__databuffer_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);

                    const aoftype = (binds.get("T") as ResolvedType).options[0];
                    const oodecl = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.object : (aoftype as ResolvedConceptAtomType).conceptTypes[0].concept;
                    const oobinds = (aoftype instanceof ResolvedEntityAtomType) ? aoftype.binds : (aoftype as ResolvedConceptAtomType).conceptTypes[0].binds;

                    const sf = (oodecl.staticFunctions.find((sfv) => sfv.name === "accepts") as StaticFunctionDecl);
                    const mirencltype = this.m_emitter.registerResolvedTypeReference(this.resolveOOTypeFromDecls(oodecl, oobinds));
                    const accepts = this.m_emitter.registerStaticCall(this.resolveOOTypeFromDecls(oodecl, oobinds), [mirencltype, oodecl, oobinds], sf, "accepts", oobinds, [], []);

                    const mirentity = new MIRDataBufferInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID, accepts);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);

                }
                else if(tdecl.attributes.includes("__ok_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);
                    
                    const mirentity = new MIRConstructableInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);

                }
                else if(tdecl.attributes.includes("__err_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("E") as ResolvedType);
                    
                    const mirentity = new MIRConstructableInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__something_type")) {
                    const miroftype = this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType);
                    
                    const mirentity = new MIRConstructableInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, miroftype.typeID);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__havoc_type")) {
                    const havocentity = new MIRHavocEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides);
                    this.m_emitter.masm.entityDecls.set(tkey, havocentity);
                }
                else if(tdecl.attributes.includes("__list_type")) {
                    const mirbinds = new Map<string, MIRType>().set("T", this.m_emitter.registerResolvedTypeReference(binds.get("T") as ResolvedType));

                    if(this.buildmode === BuildApplicationMode.ModelChecker) {
                        const llresolved = this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, new NominalTypeSignature("Core", ["ListRepr"], [new TemplateTypeSignature("T")]), binds);
                        this.m_emitter.registerResolvedTypeReference(llresolved);
                    }

                    const mirentity = new MIRPrimitiveListEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, mirbinds);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__stack_type")) {
                    assert(false);
                    //MIRPrimitiveStackEntityTypeDecl
                }
                else if(tdecl.attributes.includes("__queue_type")) {
                    assert(false);
                    //MIRPrimitiveQueueEntityTypeDecl
                }
                else if(tdecl.attributes.includes("__set_type")) {
                    assert(false);
                    //MIRPrimitiveSetEntityTypeDecl
                }
                else if(tdecl.attributes.includes("__map_type")) {
                    const mirbinds = new Map<string, MIRType>().set("K", this.m_emitter.registerResolvedTypeReference(binds.get("K") as ResolvedType)).set("V", this.m_emitter.registerResolvedTypeReference(binds.get("V") as ResolvedType));

                    if(this.buildmode === BuildApplicationMode.ModelChecker) {
                        const mmresolved = this.resolveAndEnsureTypeOnly(tdecl.sourceLocation, new NominalTypeSignature("Core", ["MapRepr"], [new TemplateTypeSignature("K"), new TemplateTypeSignature("V")]), binds);
                        this.m_emitter.registerResolvedTypeReference(mmresolved);
                    }
                    
                    const mirentity = new MIRPrimitiveMapEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, mirbinds);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else if(tdecl.attributes.includes("__internal")) { 
                    const mirentity = new MIRPrimitiveInternalEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
                else {
                    const initinfo = this.generateEntityInitializerFunctions(tdecl, binds);

                    const invenvargs = new Map<string, VarInfo>();
                    const consenvargs = new Map<string, VarInfo>();
                    const ccfields = this.m_assembly.getAllOOFieldsConstructors(tdecl, binds);
                    [...ccfields.req, ...ccfields.opt].forEach((ff) => {
                        const fdi = ff[1];
                        const ftype = this.resolveAndEnsureTypeOnly(fdi[1].sourceLocation, fdi[1].declaredType, fdi[2]);

                        invenvargs.set(`$${fdi[1].name}`, new VarInfo(ftype, fdi[1].value === undefined, false, true, ftype));
                        consenvargs.set(`$${fdi[1].name}`, new VarInfo(ftype, fdi[1].value === undefined, false, true, ftype));
                    });
                    const consfuncfields = [
                        ...[...ccfields.req].map((ccf) => {
                           return {cfkey: MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ccf[1][0], ccf[1][2]), ccf[1][1].name), isoptional: false}
                        }), 
                        ...[...ccfields.opt].map((ccf) => {
                            return {cfkey: MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(ccf[1][0], ccf[1][2]), ccf[1][1].name), isoptional: true}
                         })
                    ];

                    let validatekey: string | undefined = undefined;
                    if(initinfo.validateclauses.length !== 0) {
                        const validatebodyid = this.generateBodyID(tdecl.sourceLocation, tdecl.srcFile, "@@validateinput");
                        const validatekeyid = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(tdecl, binds), "@@validateinput", new Map<string, ResolvedType>(), []);
                        
                        const validateenv = TypeEnvironment.createInitialEnvForCall(validatekeyid.keyid, validatebodyid, binds, new Map<string, PCode>(), invenvargs, undefined);
                        this.generateInvariantCheck(validatebodyid, validateenv, validatekeyid.keyid, validatekeyid.shortname, tdecl, binds, {clauses: initinfo.validateclauses, optinits: initinfo.optinits});
                        validatekey = validatekeyid.keyid;
                    }

                    const directconsbodyid = this.generateBodyID(tdecl.sourceLocation, tdecl.srcFile, "@@directconstructor");
                    const directconskey = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(tdecl, binds), "@@directconstructor", new Map<string, ResolvedType>(), []);
                    
                    const directconsenv = TypeEnvironment.createInitialEnvForCall(directconskey.keyid, directconsbodyid, binds, new Map<string, PCode>(), consenvargs, undefined);
                    this.generateDirectConstructor(directconsbodyid, directconsenv, directconskey.keyid, directconskey.shortname, tdecl, binds, initinfo.invariantclauses);

                    const fields: MIRFieldDecl[] = [];
                    const finfos = [...this.m_assembly.getAllOOFieldsLayout(tdecl, binds)];
                    finfos.forEach((ff) => {
                        const fi = ff[1];
                        const f = fi[1];

                        const fkey = MIRKeyGenerator.generateFieldKey(this.resolveOOTypeFromDecls(fi[0], fi[2]), f.name);
                        if (!this.m_emitter.masm.fieldDecls.has(fkey)) {
                            const dtypeResolved = this.resolveAndEnsureTypeOnly(f.sourceLocation, f.declaredType, binds);
                            const dtype = this.m_emitter.registerResolvedTypeReference(dtypeResolved);

                            const mfield = new MIRFieldDecl(tkey, f.attributes, f.sourceLocation, f.srcFile, fkey, f.name, f.value !== undefined, dtype.typeID);
                            this.m_emitter.masm.fieldDecls.set(fkey, mfield);
                        }

                        fields.push(this.m_emitter.masm.fieldDecls.get(fkey) as MIRFieldDecl);
                    });

                    const initconsbodyid = this.generateBodyID(tdecl.sourceLocation, tdecl.srcFile, "@@initconstructor");
                    let initconskey: GeneratedKeyName<MIRInvokeKey> | undefined = undefined;
                    if(this.constructorHasOptionals(tdecl, binds)) {
                        initconskey = MIRKeyGenerator.generateFunctionKeyWType(this.resolveOOTypeFromDecls(tdecl, binds), "@@initconstructor", new Map<string, ResolvedType>(), []);
                        const initconsenv = TypeEnvironment.createInitialEnvForCall(initconskey.keyid, initconsbodyid, binds, new Map<string, PCode>(), consenvargs, undefined);
                        this.generateInitConstructor(initconsbodyid, initconsenv, initconskey.keyid, initconskey.shortname, tdecl, binds, initinfo.optinits, directconskey.keyid);
                    }

                    const mirentity = new MIRObjectEntityTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides, initinfo.invariantclauses.length !== 0, validatekey, initconskey !== undefined ? initconskey.keyid : undefined, directconskey.keyid, consfuncfields, fields);
                    this.m_emitter.masm.entityDecls.set(tkey, mirentity);
                }
            }
            else {
                const mirconcept = new MIRConceptTypeDecl(tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, tdecl.ns, tdecl.name, terms, provides);
                this.m_emitter.masm.conceptDecls.set(tkey, mirconcept);
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    //e.g. expressions in match-case which must be constantly evaluatable
    private processInvokeInfo_ExpressionIsolated(bodyID: string, srcFile: string, exp: Expression, ikey: MIRInvokeKey, ishort: string, sinfo: SourceInfo, attributes: string[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>): MIRInvokeDecl {
        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, []);

        const env = TypeEnvironment.createInitialEnvForCall(ikey, bodyID, binds, new Map<string, PCode>(), new Map<string, VarInfo>(), declaredResult);
            
        const mirbody = this.checkBodyExpression(srcFile, env, exp, declaredResult, []);
        return new MIRInvokeBodyDecl(undefined, bodyID, ikey, ishort, attributes, false, sinfo, sinfo, this.m_file, [], 0, resultType.typeID, undefined, undefined, mirbody as MIRBody);
    }

    //e.g. expressions as default arguments or field values which can only have other specific refs (but not pcodes or random other values)
    private processInvokeInfo_ExpressionLimitedArgs(bodyID: string, srcFile: string, exp: Expression, ikey: MIRInvokeKey, ishort: string, sinfo: SourceInfo, attributes: string[], invkparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>): MIRInvokeDecl {
        let cargs = new Map<string, VarInfo>();
        let params: MIRFunctionParameter[] = [];

        invkparams.forEach((p) => {
            assert(p.refKind === undefined);
            const mtype = this.m_emitter.registerResolvedTypeReference(p.ptype);

            cargs.set(p.name, new VarInfo(p.ptype, true, false, true, p.ptype));
            params.push(new MIRFunctionParameter(p.name, mtype.typeID));
        });

        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, invkparams.map((ivk) => { return {pname: ivk.name, isref: false, defonentry: true, ptype: ivk.ptype} }));
        const env = TypeEnvironment.createInitialEnvForCall(ikey, bodyID, binds, new Map<string, PCode>(), cargs, declaredResult);
        
        const mirbody = this.checkBodyExpression(srcFile, env, exp, declaredResult, []);
        return new MIRInvokeBodyDecl(undefined, bodyID, ikey, ishort, attributes, false, sinfo, sinfo, this.m_file, params, 0, resultType.typeID, undefined, undefined, mirbody as MIRBody);
    }

    //e.g. things like pre and post conditions
    private processInvokeInfo_ExpressionGeneral(bodyID: string, srcFile: string, exp: Expression, ikey: MIRInvokeKey, ishort: string, sinfo: SourceInfo, attributes: string[], invkparams: {name: string, ptype: ResolvedType}[], declaredResult: ResolvedType, binds: Map<string, ResolvedType>, pcodes: Map<string, PCode>, pargs: [string, ResolvedType][]): MIRInvokeDecl {
        let cargs = new Map<string, VarInfo>();
        let params: MIRFunctionParameter[] = [];

        invkparams.forEach((p) => {
            const mtype = this.m_emitter.registerResolvedTypeReference(p.ptype);

            cargs.set(p.name, new VarInfo(p.ptype, true, false, true, p.ptype));
            params.push(new MIRFunctionParameter(p.name, mtype.typeID));
        });

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(pargs[i][0], ctype.typeID));
        }

        const resultType = this.generateExpandedReturnSig(sinfo, declaredResult, invkparams.map((ivk) => { return {pname: ivk.name, isref: false, defonentry: true, ptype: ivk.ptype} }));
        const env = TypeEnvironment.createInitialEnvForCall(ikey, bodyID, binds, pcodes, cargs, declaredResult);
        
        const mirbody = this.checkBodyExpression(srcFile, env, exp, declaredResult, []);
        return new MIRInvokeBodyDecl(undefined, bodyID, ikey, ishort, attributes, false, sinfo, sinfo, this.m_file, params, 0, resultType.typeID, undefined, undefined, mirbody as MIRBody);
    }

    private processInvokeInfo(name: string, ikey: MIRInvokeKey, shortname: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, kind: "namespace" | "static" | "member" | "operator", invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], pargs: [string, ResolvedType][]): MIRInvokeDecl {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke, binds, pcodes);

        let terms = new Map<string, MIRType>();
        invoke.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name) as ResolvedType)));

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && pcodes.some((pc) => pc.code.recursive === "yes"));
        
        let cargs = new Map<string, VarInfo>();
        let fargs = new Map<string, PCode>();
        let refnames: string[] = [];
        let outparaminfo: {pname: string, isref: boolean, defonentry: boolean, ptype: ResolvedType}[] = [];
        let entrycallparams: {name: string, ptype: ResolvedType}[] = [];
        let params: MIRFunctionParameter[] = [];

        invoke.params.forEach((p) => {
            const pdecltype = this.m_assembly.normalizeTypeGeneral(p.type, binds);
            if (pdecltype instanceof ResolvedFunctionType) {
                const pcarg = pcodes[fargs.size];
                fargs.set(p.name, pcarg);
            }
            else {
                if (p.refKind !== undefined) {
                    refnames.push(p.name);

                    if (p.refKind === "out" || p.refKind === "out?") {
                        outparaminfo.push({ pname: p.name, isref: true, defonentry: false, ptype: pdecltype });
                    }
                    else {
                        outparaminfo.push({ pname: p.name, isref: true, defonentry: true, ptype: pdecltype });
                    }
                }

                if (p.refKind === undefined || p.refKind === "ref") {
                    const mtype = this.m_emitter.registerResolvedTypeReference(pdecltype);

                    cargs.set(p.name, new VarInfo(pdecltype, p.refKind === undefined, false, true, pdecltype));
                    entrycallparams.push({name: p.name, ptype: pdecltype});
                    params.push(new MIRFunctionParameter(p.name, mtype.typeID));
                }
            }
        });

        if (invoke.optRestType !== undefined) {
            const rtype = this.resolveAndEnsureTypeOnly(invoke.startSourceLocation, invoke.optRestType, binds);
            cargs.set(invoke.optRestName as string, new VarInfo(rtype, true, false, true, rtype));

            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);

            entrycallparams.push({name: invoke.optRestName as string, ptype: rtype});
            params.push(new MIRFunctionParameter(invoke.optRestName as string, resttype.typeID));
        }

        let prepostcapturednames: string[] = [];
        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(pargs[i][0], ctype.typeID));

            prepostcapturednames.push(pargs[i][0]);
        }

        let optparaminfo: {pname: string, ptype: ResolvedType, maskidx: number, initaction: InitializerEvaluationAction}[] = [];
        invoke.params.forEach((p) => {
            const pdecltype = this.m_assembly.normalizeTypeGeneral(p.type, binds);
            if (pdecltype instanceof ResolvedType && p.isOptional) {
                if (p.defaultexp === undefined) {
                    const ii = new InitializerEvaluationLiteralExpression(new LiteralNoneExpression(invoke.startSourceLocation));
                    optparaminfo.push({pname: p.name, ptype: pdecltype, maskidx: optparaminfo.length, initaction: ii});
                }
                else {
                    const ii = this.processExpressionForOptParamDefault(invoke.srcFile, p.name, pdecltype, p.defaultexp, binds, enclosingDecl, invoke);
                    optparaminfo.push({pname: p.name, ptype: pdecltype, maskidx: optparaminfo.length, initaction: ii});
                }
            }
        });

        const declaredResult = this.resolveAndEnsureTypeOnly(invoke.startSourceLocation, invoke.resultType, binds);
        const resultType = this.generateExpandedReturnSig(invoke.startSourceLocation, declaredResult, outparaminfo);

        let rprs: { name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType }[] = [];
        rprs.push({ name: "$return", refKind: undefined, ptype: declaredResult });

        let rreforig: { name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType }[] = [];
        invoke.params
        .filter((p) => p.refKind === "ref")
        .map((p) => {
                const pdecltype = this.m_assembly.normalizeTypeOnly(p.type, binds);
                rreforig.push({name: `$${p.name}`, refKind: undefined, ptype: pdecltype});
        });
        
        let preject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined = undefined;
        let postject: [{ ikey: string, sinfo: SourceInfo, srcFile: string }[], string[]] | undefined = undefined;
        let realbody = invoke.body;
        if (kind === "namespace") {
            if (invoke.preconditions.length !== 0) {
                this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.some((pre) => pre.isvalidate) && !invoke.preconditions.some((pre) => pre.isvalidate), "Cannot mix terminal and validate preconditions");

                if (invoke.preconditions.every((pre) => pre.isvalidate)) {
                    realbody = this.processGenerateSpecialPreFunction_ResultT(invoke.startSourceLocation, invoke.preconditions, invoke.body as BodyImplementation);
                }
                else {
                    const preclauses = this.processGenerateSpecialPreFunction_FailFast(entrycallparams, fargs, pargs, invoke.preconditions, binds, invoke.srcFile);
                    preject = [preclauses, [...entrycallparams.map((pp) => pp.name), ...prepostcapturednames]];
                }
            }

            if (invoke.postconditions.length !== 0) {
                const postcluases = this.processGenerateSpecialPostFunction([...entrycallparams, ...rprs, ...rreforig], fargs, pargs, invoke.postconditions, binds, invoke.srcFile);
                postject = [postcluases, [...[...entrycallparams, ...rprs, ...rreforig].map((pp) => pp.name), ...prepostcapturednames]];
            }
        }
        else {
            const ootype = (enclosingDecl as [MIRType, OOPTypeDecl, Map<string, ResolvedType>])[1];
            const oobinds = (enclosingDecl as [MIRType, OOPTypeDecl, Map<string, ResolvedType>])[2];
            const absconds = this.m_assembly.getAbstractPrePostConds(name, ootype, oobinds, binds);

            if ((absconds !== undefined && absconds.pre[0].length !== 0) || invoke.preconditions.length !== 0) {
                this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.some((pre) => pre.isvalidate) || (absconds !== undefined && absconds.pre[0].some((pre) => pre.isvalidate)), "Cannot use validate preconditions on non-entrypoint functions");

                const abspreclauses = absconds !== undefined ? this.processGenerateSpecialPreFunction_FailFast(entrycallparams, fargs, pargs, absconds.pre[0], absconds.pre[1], invoke.srcFile) : [];
                const preclauses = this.processGenerateSpecialPreFunction_FailFast(entrycallparams, fargs, pargs, invoke.preconditions, binds, invoke.srcFile);
                preject = [[...abspreclauses, ...preclauses], [...entrycallparams.map((pp) => pp.name), ...prepostcapturednames]];
            }

            if ((absconds !== undefined && absconds.post[0].length !== 0) || invoke.postconditions.length !== 0) {
                const abspostclauses = absconds !== undefined ? this.processGenerateSpecialPostFunction([...entrycallparams, ...rprs, ...rreforig], fargs, pargs, absconds.post[0], absconds.post[1], invoke.srcFile) : [];
                const postcluases = this.processGenerateSpecialPostFunction([...entrycallparams, ...rprs, ...rreforig], fargs, pargs, invoke.postconditions, binds, invoke.srcFile);
                postject = [[...abspostclauses, ...postcluases], [...[...entrycallparams, ...rprs, ...rreforig].map((pp) => pp.name), ...prepostcapturednames]];
            }
        }

        const encdecl = enclosingDecl !== undefined ? enclosingDecl[0].typeID : undefined;
        if (typeof ((invoke.body as BodyImplementation).body) === "string") {
            if ((invoke.body as BodyImplementation).body !== "default" || OOPTypeDecl.attributeSetContains("__primitive", invoke.attributes)) {
                let mbinds = new Map<string, MIRResolvedTypeKey>();
                binds.forEach((v, k) => mbinds.set(k, this.m_emitter.registerResolvedTypeReference(v).typeID));

                let mpc = new Map<string, MIRPCode>();
                fargs.forEach((v, k) => {
                    const cargs = [...v.captured].map((cv) => { 
                        const capturedname = this.m_emitter.generateCapturedVarName(cv[0], v.code.bodyID);
                        return {cname: capturedname, ctype: cv[1].typeID}; 
                    });

                    if(v.capturedpcode.size !== 0) {
                        const pcc = this.m_emitter.flattenCapturedPCodeVarCapturesWithTypes(v.capturedpcode);
                        pcc.forEach((vv) => {
                            cargs.push(vv);
                        });
                    }

                    mpc.set(k, { code: v.ikey, cargs: cargs })
                });

                return new MIRInvokePrimitiveDecl(encdecl, invoke.bodyID, ikey, shortname, invoke.attributes, recursive, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, mbinds, params, resultType.typeID, (invoke.body as BodyImplementation).body as string, mpc);
            }
            else {
                //
                //TODO: support typed numbers with default
                //
                assert(false, "We only handle 'default' ops on primitive types -- need to do better to support TypedNumbers");
                
                return new MIRInvokePrimitiveDecl(encdecl, invoke.bodyID, ikey, shortname, invoke.attributes, recursive, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, new Map<string, string>(), [], resultType.typeID, "[INVALID]", new Map<string, MIRPCode>());
            }
        }
        else {
            const env = TypeEnvironment.createInitialEnvForCall(ikey, invoke.bodyID, binds, fargs, cargs, declaredResult);

            const mirbody = this.checkBodyStatement(invoke.srcFile, env, (realbody as BodyImplementation).body as BlockStatement, declaredResult, optparaminfo, outparaminfo, preject, postject);
            return new MIRInvokeBodyDecl(encdecl, invoke.bodyID, ikey, shortname, invoke.attributes, recursive, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, params, optparaminfo.length, resultType.typeID, preject !== undefined ? preject[0].map((pc) => pc.ikey) : undefined, postject !== undefined ? postject[0].map((pc) => pc.ikey) : undefined, mirbody as MIRBody);
        }
    }

    private processPCodeInfo(ikey: MIRInvokeKey, shortname: string, pci: InvokeDecl, binds: Map<string, ResolvedType>, fsig: ResolvedFunctionType, pargs: [string, ResolvedType][], capturedpcodes: [string, PCode][]): MIRInvokeDecl {
        this.checkPCodeDecl(pci.startSourceLocation, fsig, pci.recursive, capturedpcodes.map((cpc) => cpc[1]));

        let cargs = new Map<string, VarInfo>();
        let refnames: string[] = [];
        let outparaminfo: {pname: string, isref: boolean, defonentry: boolean, ptype: ResolvedType}[] = [];
        let entrycallparams: {name: string, refKind: "ref" | "out" | "out?" | undefined, ptype: ResolvedType}[] = [];
        let params: MIRFunctionParameter[] = [];

        pci.params.forEach((p, i) => {
            const pdecltype = fsig.params[i].type as ResolvedType;
            if (p.refKind !== undefined) {
                refnames.push(p.name);

                if (p.refKind === "out" || p.refKind === "out?") {
                    outparaminfo.push({ pname: p.name, isref: true, defonentry: false, ptype: pdecltype });
                }
                else {
                    outparaminfo.push({ pname: p.name, isref: true, defonentry: true, ptype: pdecltype });
                }
            }

            if (p.refKind === undefined || p.refKind === "ref") {
                const mtype = this.m_emitter.registerResolvedTypeReference(pdecltype);

                cargs.set(p.name, new VarInfo(pdecltype, p.refKind === undefined, false, true, pdecltype));

                entrycallparams.push({ name: p.name, refKind: p.refKind, ptype: pdecltype });
                params.push(new MIRFunctionParameter(p.name, mtype.typeID));
            }
        });

        if (pci.optRestType !== undefined) {
            const rtype = fsig.optRestParamType as ResolvedType;
            cargs.set(pci.optRestName as string, new VarInfo(rtype, true, false, true, rtype));

            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);
            entrycallparams.push({name: pci.optRestName as string, refKind: undefined, ptype: rtype});
            params.push(new MIRFunctionParameter(pci.optRestName as string, resttype.typeID));
        }

        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new VarInfo(pargs[i][1], true, true, true, pargs[i][1]));

            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            params.push(new MIRFunctionParameter(pargs[i][0], ctype.typeID));
        }

        let resolvedResult = fsig.resultType;
        const resultType = this.generateExpandedReturnSig(pci.startSourceLocation, resolvedResult, outparaminfo);

        const realbody = ((pci.body as BodyImplementation).body instanceof Expression) 
            ? new BlockStatement(pci.startSourceLocation, [new ReturnStatement(pci.startSourceLocation, [(pci.body as BodyImplementation).body as Expression])])
            : ((pci.body as BodyImplementation).body as BlockStatement);

        let pcodes = new Map<string, PCode>();
        capturedpcodes.forEach((cpc) => {
            pcodes.set(cpc[0], cpc[1]);
        });
        const env = TypeEnvironment.createInitialEnvForCall(ikey, pci.bodyID, binds, pcodes, cargs, fsig.resultType);

        const mirbody = this.checkBodyStatement(pci.srcFile, env, realbody, fsig.resultType, [], outparaminfo, undefined, undefined);
        return new MIRInvokeBodyDecl(undefined, pci.bodyID, ikey, shortname, pci.attributes, pci.recursive === "yes", pci.startSourceLocation, pci.endSourceLocation, pci.srcFile, params, 0, resultType.typeID, undefined, undefined, mirbody as MIRBody);
    }

    processConstExpr(gkey: MIRGlobalKey, shortname: string, name: string, srcFile: string, containingType: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, cexp: ConstantExpressionValue, attribs: string[], binds: Map<string, ResolvedType>, ddecltype: ResolvedType) {
        try {
            const bodyid = this.generateBodyID(cexp.exp.sinfo, srcFile, "constexp");
            const ikeyinfo = MIRKeyGenerator.generateFunctionKeyWNamespace(bodyid /*not ns but sure*/, name, binds, [], "constexp");

            const idecl = this.processInvokeInfo_ExpressionIsolated(bodyid, srcFile, cexp.exp, ikeyinfo.keyid, ikeyinfo.shortname, cexp.exp.sinfo, attribs, ddecltype, binds);
            this.m_emitter.masm.invokeDecls.set(ikeyinfo.keyid, idecl as MIRInvokeBodyDecl);

            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const mirconst = new MIRConstantDecl(containingType !== undefined ? containingType[0].typeID : undefined, gkey, shortname, attribs, cexp.exp.sinfo, srcFile, dtype.typeID, ikeyinfo.keyid);

            this.m_emitter.masm.constantDecls.set(gkey, mirconst);
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processFunctionDecl(fkey: MIRInvokeKey, shortname: string, name: string, enclosingdecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = invoke.srcFile;
            const invinfo = this.processInvokeInfo(name, fkey, shortname, enclosingdecl, enclosingdecl === undefined ? "namespace" : "static", invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(fkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(fkey, invinfo as MIRInvokeBodyDecl);
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processLambdaFunction(lkey: MIRInvokeKey, lshort: string, invoke: InvokeDecl, sigt: ResolvedFunctionType, bodybinds: Map<string, ResolvedType>, cargs: [string, ResolvedType][], capturedpcodes: [string, PCode][]) {
        try {
            this.m_file = invoke.srcFile;
            const invinfo = this.processPCodeInfo(lkey, lshort, invoke, bodybinds, sigt, cargs, capturedpcodes);

            this.m_emitter.masm.invokeDecls.set(lkey, invinfo as MIRInvokeBodyDecl);
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processMethodFunction(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        if (this.m_emitter.masm.invokeDecls.has(mkey)) {
            return;
        }

        try {
            this.m_file = mdecl.srcFile;
            const invinfo = this.processInvokeInfo(name, mkey, shortname, enclosingDecl, "member", mdecl.invoke, binds, pcodes, cargs);

            this.m_emitter.masm.invokeDecls.set(mkey, invinfo as MIRInvokeBodyDecl);

            if(mdecl.invoke.attributes.includes("override") || mdecl.invoke.attributes.includes("virtual")) {
                const tkey = MIRKeyGenerator.generateTypeKey(this.resolveOOTypeFromDecls(enclosingDecl[1], enclosingDecl[2]));
                (this.m_emitter.masm.entityDecls.get(tkey) as MIRObjectEntityTypeDecl).vcallMap.set(vkey, mkey);
            }
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    processVirtualOperator(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [ResolvedType, MIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
        try {
            this.m_file = invoke.srcFile;
            const vopencl = enclosingDecl !== undefined ? ([enclosingDecl[1], enclosingDecl[2], enclosingDecl[3]] as [MIRType, OOPTypeDecl, Map<string, ResolvedType>]) : undefined;
            const invinfo = this.processInvokeInfo(name, mkey, shortname, vopencl, "operator", invoke, binds, pcodes, cargs);

            if (invinfo instanceof MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(mkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(mkey, invinfo as MIRInvokeBodyDecl);
            }

            if(!this.m_emitter.masm.virtualOperatorDecls.has(vkey)) {
                this.m_emitter.masm.virtualOperatorDecls.set(vkey, []);
            }
            (this.m_emitter.masm.virtualOperatorDecls.get(vkey) as MIRInvokeKey[]).push(mkey);
        }
        catch (ex) {
            this.m_emitter.setEmitEnabled(false);
            this.abortIfTooManyErrors();
        }
    }

    private resolveREExp(sinfo: SourceInfo, cre: RegexConstClass): RegexComponent {
        this.raiseErrorIf(sinfo, !this.m_assembly.hasNamespace(cre.ns), "Namespace not found");
        const ns = this.m_assembly.getNamespace(cre.ns);

        this.raiseErrorIf(sinfo, !ns.consts.has(cre.ccname), "Const name not found");
        const cc = ns.consts.get(cre.ccname) as NamespaceConstDecl;

        if(cc.value.exp instanceof LiteralRegexExpression) {
            return cc.value.exp.value.re;
        }
        else {
            this.raiseErrorIf(sinfo, !(cc.value.exp instanceof AccessNamespaceConstantExpression), "Only literals and other const references allowed");

            const cca = cc.value.exp as AccessNamespaceConstantExpression;
            return this.resolveREExp(sinfo, new RegexConstClass(cca.ns, cca.name));
        }
    }

    private processRegexComponent(sinfo: SourceInfo, rr: RegexComponent): RegexComponent {
        if((rr instanceof RegexLiteral) || (rr instanceof RegexCharRange) || (rr instanceof RegexDotCharClass)) {
            return rr;
        } 
        else if (rr instanceof RegexConstClass) {
            return this.resolveREExp(sinfo, rr);
        } 
        else if (rr instanceof RegexStarRepeat) {
            return new RegexStarRepeat(this.processRegexComponent(sinfo, rr.repeat));
        } 
        else if (rr instanceof RegexPlusRepeat) {
            return new RegexPlusRepeat(this.processRegexComponent(sinfo, rr.repeat));
        } 
        else if (rr instanceof RegexRangeRepeat) {
            return new RegexRangeRepeat(this.processRegexComponent(sinfo, rr.repeat), rr.min, rr.max);
        } 
        else if (rr instanceof RegexOptional) {
            return new RegexOptional(this.processRegexComponent(sinfo, rr.opt));
        } 
        else if (rr instanceof RegexAlternation) {
            return new RegexAlternation(rr.opts.map((ropt) => this.processRegexComponent(sinfo, ropt)));
        } 
        else {
            assert(rr instanceof RegexSequence);
            return new RegexSequence((rr as RegexSequence).elems.map((relem) => this.processRegexComponent(sinfo, relem)));
        }
    }

    processRegexInfo() {
        const emptysinfo = new SourceInfo(-1, -1, -1, -1);
        this.m_assembly.getAllLiteralRegexs().forEach((lre) => {
            const rr = this.processRegexComponent(emptysinfo, lre.re);
            this.m_emitter.masm.literalRegexs.push(new BSQRegex(lre.restr, rr));
        });

        this.m_assembly.getAllValidators().forEach((vre) => {
            const rr = this.processRegexComponent(emptysinfo, vre[1].re);

            const vkey = MIRKeyGenerator.generateTypeKey(ResolvedType.createSingle(vre[0]));
            this.m_emitter.masm.validatorRegexs.set(vkey, new BSQRegex(vre[1].restr, rr));
        });
    }
}

export { TypeError, TypeChecker };
