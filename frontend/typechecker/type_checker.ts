//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { Assembly, BuildLevel, ConceptTypeDecl, EntityTypeDecl, InvariantDecl, InvokeDecl, isBuildLevelEnabled, MemberFieldDecl, MemberMethodDecl, NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, NamespaceTypedef, OOMemberDecl, OOPTypeDecl, PathValidator, PreConditionDecl, StaticFunctionDecl, StaticMemberDecl, TaskEffectFlag, TaskTypeDecl, TemplateTermDecl, TypeConditionRestriction, ValidateDecl } from "../ast/assembly";
import { ResolvedASCIIStringOfEntityAtomType, ResolvedAtomType, ResolvedConceptAtomType, ResolvedConceptAtomTypeEntry, ResolvedOkEntityAtomType, ResolvedErrEntityAtomType, ResolvedSomethingEntityAtomType, ResolvedMapEntryEntityAtomType, ResolvedEntityAtomType, ResolvedEnumEntityAtomType, ResolvedEphemeralListType, ResolvedFunctionType, ResolvedHavocEntityAtomType, ResolvedListEntityAtomType, ResolvedMapEntityAtomType, ResolvedObjectEntityAtomType, ResolvedPathEntityAtomType, ResolvedPathFragmentEntityAtomType, ResolvedPathGlobEntityAtomType, ResolvedPathValidatorEntityAtomType, ResolvedPrimitiveInternalEntityAtomType, ResolvedQueueEntityAtomType, ResolvedRecordAtomType, ResolvedSetEntityAtomType, ResolvedStackEntityAtomType, ResolvedStringOfEntityAtomType, ResolvedTaskAtomType, ResolvedTupleAtomType, ResolvedType, ResolvedTypedeclEntityAtomType, ResolvedValidatorEntityAtomType, TemplateBindScope, ResolvedFunctionTypeParam, ResolvedInternalEntityAtomType, ResolvedConstructableEntityAtomType, ResolvedPrimitiveCollectionEntityAtomType } from "./resolved_type";
import { AccessEnvValueExpression, AccessFormatInfoExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndxpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionExpression, ConstantExpressionValue, ConstructorEphemeralValueList, ConstructorPCodeExpression, ConstructorPrimaryExpression, ConstructorRecordExpression, ConstructorTupleExpression, Expression, ExpressionTag, IfExpression, InvalidExpression, LiteralASCIIStringExpression, LiteralASCIITemplateStringExpression, LiteralASCIITypedStringExpression, LiteralBoolExpression, LiteralExpressionValue, LiteralFloatPointExpression, LiteralIntegralExpression, LiteralNoneExpression, LiteralNothingExpression, LiteralRationalExpression, LiteralRegexExpression, LiteralStringExpression, LiteralTemplateStringExpression, LiteralTypedPrimitiveConstructorExpression, LiteralTypedStringExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchExpression, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, PCodeInvokeExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAs, PostfixInvoke, PostfixIs, PostfixOp, PostfixOperation, PostfixOpTag, PrefixNegateOp, PrefixNotOp, SpecialConstructorExpression, SwitchExpression, TaskSelfFieldExpression, TaskSelfActionExpression, TaskGetIDExpression, EmptyStatement, VariableDeclarationStatement, MultiReturnWithDeclarationStatement, VariableAssignmentStatement, MultiReturnWithAssignmentStatement, ReturnStatement, AbortStatement, AssertStatement } from "../ast/body";
import { AndTypeSignature, AutoTypeSignature, EphemeralListTypeSignature, FunctionTypeSignature, NominalTypeSignature, ParseErrorTypeSignature, ProjectTypeSignature, RecordTypeSignature, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature } from "../ast/type";
import { FlowTypeTruthOps, ExpressionTypeEnvironment, VarInfo, FlowTypeTruthValue, FlowTypeInfoOption, StatementTypeEnvironment } from "./type_environment";

import { TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessConstMemberFieldExpression, TIRAccessVariableExpression, TIRExpression, TIRInvalidExpression, TIRLiteralASCIIStringExpression, TIRLiteralASCIITemplateStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression, TIRLiteralStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralTypedPrimitiveConstructorExpression, TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedStringExpression, TIRLiteralValue, TIRCoerceSafeExpression, TIRCoerceSafeRefCallResultExpression, TIRCoerceSafeTaskRefCallResultExpression, TIRCoerceSafeActionCallResultExpression, TIRConstructorPrimaryDirectExpression, TIRResultOkConstructorExpression, TIRResultErrConstructorExpression, TIRSomethingConstructorExpression, TIRMapEntryConstructorExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorListExpression, TIRConstructorMapExpression, TIRConstructorTupleExpression, TIRConstructorRecordExpression, TIRConstructorEphemeralValueList, TIRCodePack, TIRTypedeclDirectExpression, TIRTypedeclConstructorExpression, TIRCallNamespaceFunctionExpression, TIRCallNamespaceFunctionWithChecksExpression, TIRCallNamespaceOperatorExpression, TIRCallNamespaceOperatorWithChecksExpression, TIRBinKeyEqBothUniqueExpression, TIRBinKeyEqOneUniqueExpression, TIRBinKeyEqGeneralExpression, TIRBinKeyUniqueLessExpression, TIRBinKeyGeneralLessExpression, TIRInjectExpression, TIRCallStaticFunctionExpression, TIRCallStaticFunctionWithChecksExpression, TIRLogicActionAndExpression, TIRIsTypeExpression, TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression, TIRIsNoneExpression, TIRIsNotNoneExpression, TIRIsNothingExpression, TIRIsSubTypeExpression, TIRAsNoneExpression, TIRAsNotNoneExpression, TIRAsNothingExpression, TIRAsTypeExpression, TIRAsSubTypeExpression, TIRExtractExpression, TIRCallMemberFunctionSelfRefWithChecksExpression, TIRCallMemberFunctionWithChecksExpression, TIRCallMemberFunctionSelfRefExpression, TIRCallMemberFunctionExpression, TIRCallMemberFunctionDynamicExpression, TIRCallMemberFunctionDynamicWithChecksExpression, TIRPrefixNotOp, TIRStatement, TIRPrefixNegateOp, TIRIsNotNothingExpression, TIRIsNotTypeExpression, TIRIsNotSubTypeExpression, TIRBinKeyNeqBothUniqueExpression, TIRBinKeyNeqOneUniqueExpression, TIRBinKeyNeqGeneralExpression, TIRIsTypeCheckAlwaysExpression, TIRIsNotTypeCheckAlwaysExpression, TIRLogicActionOrExpression, TIRBinLogicAndxpression, TIRBinLogicOrExpression, TIRBinAddExpression, TIRBinSubExpression, TIRBinMultExpression, TIRBinDivExpression, TIRNumericEqExpression, TIRNumericNeqExpression, TIRNumericLessExpression, TIRNumericLessEqExpression, TIRNumericGreaterExpression, TIRNumericGreaterEqExpression, TIRIfExpression, TIRSwitchExpression, TIRMatchExpression, TIRTaskSelfFieldExpression, TIRTaskGetIDExpression, TIRCallMemberActionExpression, TIRVarDeclareStatement, TIRCallMemberFunctionTaskSelfRefExpression, TIRCallMemberFunctionTaskExpression, TIRMultiVarDeclareAndAssignStatement, TIRVarDeclareAndAssignStatementWRef, TIRVarDeclareAndAssignStatementWTaskRef, TIRVarDeclareAndAssignStatementWAction, TIRVarDeclareAndAssignStatement, TIRMultiVarDeclareStatement, TIRPackMultiExpression, TIRCoerceSafeMultiExpression, TIRMultiVarDeclareAndAssignStatementWRef, TIRMultiVarDeclareAndAssignStatementWTaskRef, TIRPackMultiExpressionWRef, TIRCoerceRefCallMultiResultExpression, TIRPackMultiExpressionWTaskRef, TIRCoerceTaskRefCallMultiResultExpression, TIRPackMultiExpressionWAction, TIRMultiVarDeclareAndAssignStatementWAction, TIRCoerceActionCallMultiResultExpression, TIRVarAssignStatementWRef, TIRVarAssignStatementWTaskRef, TIRVarAssignStatementWAction, TIRVarAssignStatement, TIRMultiVarAssignStatement, TIRMultiVarAssignStatementWAction, TIRMultiVarAssignStatementWTaskRef, TIRMultiVarAssignStatementWRef, TIRReturnStatement, TIRAbortStatement } from "../tree_ir/tir_body";
import { TIRASCIIStringOfEntityType, TIRConceptSetType, TIRConceptType, TIREntityType, TIREnumEntityType, TIREphemeralListType, TIRErrEntityType, TIRFieldKey, TIRHavocEntityType, TIRInvariantDecl, TIRInvokeKey, TIRListEntityType, TIRMapEntityTIRType, TIRMapEntryEntityType, TIRMemberConstKey, TIRMemberFieldDecl, TIRNamespaceMemberName, TIRObjectEntityType, TIROkEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRSomethingEntityType, TIRStackEntityType, TIRStringOfEntityType, TIRTaskEffectFlag, TIRTaskEnvironmentEffect, TIRTaskResourceEffect, TIRTaskType, TIRTupleType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRTypeMemberName, TIRTypeName, TIRUnionType, TIRValidateDecl, TIRValidatorEntityType } from "../tree_ir/tir_assembly";

import { BSQRegex } from "../bsqregex";
import { extractLiteralStringValue, extractLiteralASCIIStringValue, SourceInfo } from "../build_decls";

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

    static generateInvokeIDForPreCondition(tinv: TIRInvokeKey, pcidx: number): TIRInvokeKey {
        xxxx;
    }

    static generateInvokeIDForPostCondition(tinv: TIRInvokeKey, pcidx: number): TIRInvokeKey {
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

    static generateInvokeIDForNamespaceOperatorBase(ns: string, name: string): TIRInvokeKey {
        return `operator_base_${ns}$${name}`;
    }

    static generateInvokeIDForNamespaceOperatorImpl(ns: string, name: string, idx: number): TIRInvokeKey {
        return `operator_impl_${idx}_${ns}$${name}`;
    }

    static generateInvokeForMemberFunction(ttype: TIRTypeKey, name: string, terms: string[]): TIRInvokeKey {
        return xxxx;
    }

    static generateInvokeForMemberMethod(ttype: TIRTypeKey, name: string, terms: string[]): TIRInvokeKey {
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
    private m_rtypes: ResolvedType[];
    private m_taskOpsOk: boolean;
    private m_taskSelfOk: "no" | "read" | "write";
    private m_taskType: {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>} | undefined;
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
    private m_pendingNamespaceFunctions: {decl: NamespaceFunctionDecl, binds: Map<string, ResolvedType>}[] = [];
    private m_pendingNamespaceOperators: {decl: NamespaceOperatorDecl, impls: NamespaceOperatorDecl[]}[] = [];

    private m_pendingConstMemberDecls: OOMemberLookupInfo<StaticMemberDecl>[] = [];
    private m_pendingFunctionMemberDecls: {decl: OOMemberLookupInfo<StaticFunctionDecl>, binds: Map<string, ResolvedType>}[] = [];
    private m_pendingMethodMemberDecls: {decl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>}[] = [];

    constructor(assembly: Assembly, buildlevel: BuildLevel, sortedSrcFiles: {fullname: string, shortname: string}[]) {
        this.m_assembly = assembly;

        this.m_buildLevel = buildlevel;

        this.m_file = "[No File]";
        this.m_rtypes = [];
        this.m_taskOpsOk = false;
        this.m_taskSelfOk = "no";
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

    private envExpressionGetInferType(env: ExpressionTypeEnvironment): ResolvedType {
        if(env.flowinfo.length === 0) {
            return ResolvedType.createInvalid();
        }
        else if(env.flowinfo.length === 1) {
            return env.flowinfo[0].tinfer;
        }
        else {
            return this.normalizeUnionList(env.flowinfo.map((fi) => fi.tinfer));
        }
    }

    private envExpressionGetInferTruth(env: ExpressionTypeEnvironment): FlowTypeTruthValue {
        if(env.flowinfo.length === 0) {
            return FlowTypeTruthValue.Unknown;
        }
        else if(env.flowinfo.length === 1) {
            return env.flowinfo[0].etruth;
        }
        else {
            if(env.flowinfo.every((fi) => fi.etruth === FlowTypeTruthValue.True)) {
                return FlowTypeTruthValue.True;
            }
            else if(env.flowinfo.every((fi) => fi.etruth === FlowTypeTruthValue.False)) {
                return FlowTypeTruthValue.False;
            }
            else {
                return FlowTypeTruthValue.Unknown;
            }
        }
    }

    private envExpressionSimplifyFlowInfos(infos: FlowTypeInfoOption[]): FlowTypeInfoOption[] {
        let ninfos: FlowTypeInfoOption[] = [];
        for(let i = 0; i < infos.length; ++i) {
            const ii = infos[i];
            const fe = ninfos.find((fi) => fi.etruth === ii.etruth && fi.tinfer.isSameType(ii.tinfer) && FlowTypeInfoOption.equivInferMaps(fi.expInferInfo, ii.expInferInfo));
            if(fe === undefined) {
                ninfos.push(ii);
            }
        }

        return ninfos;
    }

    private envClearExps(env: ExpressionTypeEnvironment, ...vars: string[]): ExpressionTypeEnvironment {
        const ftti = this.envExpressionSimplifyFlowInfos(env.flowinfo.map((ffi) => ffi.clearVars(vars)));
        return env.updateFromClearVars(ftti);
    }

    private setResultExpression(env: ExpressionTypeEnvironment, exp: TIRExpression, trepr: ResolvedType, tv?: FlowTypeTruthValue | undefined): ExpressionTypeEnvironment {
        const finfo = env.flowinfo.map((fti) => {
            let tinfer = trepr;
            let value = tv || FlowTypeTruthValue.Unknown;
            if(fti.expInferInfo.has(exp.expstr)) {
                const einfo = fti.expInferInfo.get(exp.expstr) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue};
                tinfer = einfo.infertype;
                value = einfo.infertruth;
            }

            assert(this.subtypeOf(tinfer, trepr), `That should be impossible -- ${tinfer.typeID} not subtype of ${trepr.typeID}`);
            return new FlowTypeInfoOption(tinfer, value, fti.expInferInfo);
        });

        return env.setResultExpressionInfo(exp, trepr, finfo);
    }

    private setResultExpressionBoolPassThrough(env: ExpressionTypeEnvironment, exp: TIRExpression, trepr: ResolvedType): ExpressionTypeEnvironment {
        const finfo = env.flowinfo.map((fti) => {
            let tinfer = trepr;
            let value = fti.etruth;
            if(fti.expInferInfo.has(exp.expstr)) {
                const einfo = fti.expInferInfo.get(exp.expstr) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue};
                tinfer = einfo.infertype;
                value = einfo.infertruth;
            }

            assert(this.subtypeOf(tinfer, trepr), `That should be impossible -- ${tinfer.typeID} not subtype of ${trepr.typeID}`);
            return new FlowTypeInfoOption(tinfer, value, fti.expInferInfo);
        });

        return env.setResultExpressionInfo(exp, trepr, finfo);
    }

    private setResultExpressionBoolNegate(env: ExpressionTypeEnvironment, exp: TIRExpression, trepr: ResolvedType): ExpressionTypeEnvironment {
        const finfo = env.flowinfo.map((fti) => {
            let tinfer = trepr;
            let value = FlowTypeTruthOps.logicalNot(fti.etruth);
            if(fti.expInferInfo.has(exp.expstr)) {
                const einfo = fti.expInferInfo.get(exp.expstr) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue};
                tinfer = einfo.infertype;
                value = einfo.infertruth;
            }

            assert(this.subtypeOf(tinfer, trepr), `That should be impossible -- ${tinfer.typeID} not subtype of ${trepr.typeID}`);
            return new FlowTypeInfoOption(tinfer, value, fti.expInferInfo);
        });

        return env.setResultExpressionInfo(exp, trepr, finfo);
    }

    private convertToBoolFlowsOnResult(env: ExpressionTypeEnvironment): {tenvs: FlowTypeInfoOption[], fenvs: FlowTypeInfoOption[]} {
        assert(this.envExpressionGetInferType(env).typeID === "Bool");

        let tenv: FlowTypeInfoOption[] = env.flowinfo
            .filter((fi) => FlowTypeTruthOps.maybeTrueValue(fi.etruth))
            .map((fi) => fi.inferFlowInfo(env.expressionResult, fi.tinfer, FlowTypeTruthValue.True));

        let fenv: FlowTypeInfoOption[] = env.flowinfo
            .filter((fi) => FlowTypeTruthOps.maybeFalseValue(fi.etruth))
            .map((fi) => fi.inferFlowInfo(env.expressionResult, fi.tinfer, FlowTypeTruthValue.False));

        return {tenvs: tenv, fenvs: fenv};
    }

    private convertToTypeNotTypeFlowsOnResult(withtype: ResolvedType, env: ExpressionTypeEnvironment): {tenvs: FlowTypeInfoOption[], fenvs: FlowTypeInfoOption[]} {
        let tenv: FlowTypeInfoOption[] = [];
        let fenv: FlowTypeInfoOption[] = [];
        
        env.flowinfo.forEach((fi) => {
            const pccs = this.splitTypes(fi.tinfer, withtype);

            if(pccs.tp !== undefined) {
                tenv.push(fi.inferFlowInfo(env.expressionResult, pccs.tp, fi.etruth));
            }

            if(pccs.fp !== undefined) {
                fenv.push(fi.inferFlowInfo(env.expressionResult, pccs.fp, fi.etruth));
            }
        });

        return {tenvs: tenv, fenvs: fenv};
    }

    private splitOnTypeCheckIs(sinfo: SourceInfo, env: ExpressionTypeEnvironment, oftype: ResolvedType): {chkexp: TIRExpression, tenvs: FlowTypeInfoOption[], fenvs: FlowTypeInfoOption[]} {
        const tiroftype = this.toTIRTypeKey(oftype);

        const renvs = this.convertToTypeNotTypeFlowsOnResult(oftype, env);
        this.raiseErrorIf(sinfo, (renvs.tenvs.length === 0 || renvs.fenvs.length === 0), `typecheck is always ${renvs.fenvs.length === 0 ? "true" : "false"}`);

        if (oftype.isNoneType()) {
            return { chkexp: new TIRIsNoneExpression(sinfo, env.expressionResult), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
        else if (oftype.isSomeType()) {
            return { chkexp: new TIRIsNotNoneExpression(sinfo, env.expressionResult), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
        else if (oftype.isNothingType()) {
            return { chkexp: new TIRIsNothingExpression(sinfo, env.expressionResult), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
        else if (oftype.options.length === 1 && ResolvedType.isUniqueType(oftype)) {
            return { chkexp: new TIRIsTypeExpression(sinfo, env.expressionResult, tiroftype), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
        else {
            return { chkexp: new TIRIsSubTypeExpression(sinfo, env.expressionResult, tiroftype), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
    }

    private processTypeIs(sinfo: SourceInfo, env: ExpressionTypeEnvironment, oftype: ResolvedType): ExpressionTypeEnvironment {
        const splits = this.splitOnTypeCheckIs(sinfo, env, oftype);

        const tflows = splits.tenvs.map((tf) => tf.inferFlowInfo(splits.chkexp, this.getSpecialBoolType(), FlowTypeTruthValue.True));
        const fflows = splits.tenvs.map((tf) => tf.inferFlowInfo(splits.chkexp, this.getSpecialBoolType(), FlowTypeTruthValue.False));

        return env.setResultExpressionInfo(splits.chkexp, this.getSpecialBoolType(), this.envExpressionSimplifyFlowInfos([...tflows, ...fflows]));
    }

    private processTypeIsFromEquality(sinfo: SourceInfo, eqop: TIRExpression, env: ExpressionTypeEnvironment, oftype: ResolvedType): ExpressionTypeEnvironment {
        const splits = this.convertToTypeNotTypeFlowsOnResult(oftype, env);
        assert((splits.tenvs.length === 0 || splits.fenvs.length === 0), "This should never fail since we check for type compatibility on eq before this");

        const tflows = splits.tenvs.map((tf) => tf.inferFlowInfo(eqop, this.getSpecialBoolType(), FlowTypeTruthValue.Unknown)); //could still be false on value equality
        const fflows = splits.tenvs.map((tf) => tf.inferFlowInfo(eqop, this.getSpecialBoolType(), FlowTypeTruthValue.False));

        return env.setResultExpressionInfo(eqop, this.getSpecialBoolType(), this.envExpressionSimplifyFlowInfos([...tflows, ...fflows]));
    }

    private splitOnTypeCheckIsNot(sinfo: SourceInfo, env: ExpressionTypeEnvironment, oftype: ResolvedType): {chkexp: TIRExpression, tenvs: FlowTypeInfoOption[], fenvs: FlowTypeInfoOption[]} {
        const tiroftype = this.toTIRTypeKey(oftype);

        const renvs = this.convertToTypeNotTypeFlowsOnResult(oftype, env);
        this.raiseErrorIf(sinfo, (renvs.tenvs.length === 0 || renvs.fenvs.length === 0), `typecheck is always ${renvs.fenvs.length === 0 ? "true" : "false"}`);

        if (oftype.isNoneType()) {
            return { chkexp: new TIRIsNotNoneExpression(sinfo, env.expressionResult), tenvs: renvs.fenvs, fenvs: renvs.tenvs };
        }
        else if (oftype.isSomeType()) {
            return { chkexp: new TIRIsNoneExpression(sinfo, env.expressionResult), tenvs: renvs.fenvs, fenvs: renvs.tenvs };
        }
        else if (oftype.isNothingType()) {
            return { chkexp: new TIRIsNotNothingExpression(sinfo, env.expressionResult), tenvs: renvs.fenvs, fenvs: renvs.tenvs };
        }
        else if (oftype.options.length === 1 && ResolvedType.isUniqueType(oftype)) {
            return { chkexp: new TIRIsNotTypeExpression(sinfo, env.expressionResult, tiroftype), tenvs: renvs.fenvs, fenvs: renvs.tenvs };
        }
        else {
            return { chkexp: new TIRIsNotSubTypeExpression(sinfo, env.expressionResult, tiroftype), tenvs: renvs.fenvs, fenvs: renvs.tenvs };
        }
    }

    private processTypeIsNot(sinfo: SourceInfo, env: ExpressionTypeEnvironment, oftype: ResolvedType): ExpressionTypeEnvironment {
        const splits = this.splitOnTypeCheckIsNot(sinfo, env, oftype);

        const tflows = splits.tenvs.map((tf) => tf.inferFlowInfo(splits.chkexp, this.getSpecialBoolType(), FlowTypeTruthValue.True));
        const fflows = splits.tenvs.map((tf) => tf.inferFlowInfo(splits.chkexp, this.getSpecialBoolType(), FlowTypeTruthValue.False));

        return env.setResultExpressionInfo(splits.chkexp, this.getSpecialBoolType(), this.envExpressionSimplifyFlowInfos([...tflows, ...fflows]));
    }

    private processTypeIsNotFromEquality(sinfo: SourceInfo, eqop: TIRExpression, env: ExpressionTypeEnvironment, oftype: ResolvedType): ExpressionTypeEnvironment {
        const splits = this.convertToTypeNotTypeFlowsOnResult(oftype, env);
        assert((splits.tenvs.length === 0 || splits.fenvs.length === 0), "This should never fail since we check for type compatibility on eq before this");

        const tflows = splits.tenvs.map((tf) => tf.inferFlowInfo(eqop, this.getSpecialBoolType(), FlowTypeTruthValue.False)); 
        const fflows = splits.tenvs.map((tf) => tf.inferFlowInfo(eqop, this.getSpecialBoolType(), FlowTypeTruthValue.Unknown)); //could still be false on value equality

        return env.setResultExpressionInfo(eqop, this.getSpecialBoolType(), this.envExpressionSimplifyFlowInfos([...tflows, ...fflows]));
    }

    private splitOnTypeCheckAs(sinfo: SourceInfo, env: ExpressionTypeEnvironment, oftype: ResolvedType): {chkexp: TIRExpression, tenvs: FlowTypeInfoOption[], fenvs: FlowTypeInfoOption[]} {
        const tiroftype = this.toTIRTypeKey(oftype);

        const renvs = this.convertToTypeNotTypeFlowsOnResult(oftype, env);
        this.raiseErrorIf(sinfo, (renvs.tenvs.length === 0 || renvs.fenvs.length === 0), `typecheck is always ${renvs.fenvs.length === 0 ? "true" : "false"}`);

        if (oftype.isNoneType()) {
            return { chkexp: new TIRAsNoneExpression(sinfo, env.expressionResult), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
        else if (oftype.isSomeType()) {
            return { chkexp: new TIRAsNotNoneExpression(sinfo, env.expressionResult), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
        else if (oftype.isNothingType()) {
            return { chkexp: new TIRAsNothingExpression(sinfo, env.expressionResult), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
        else if (oftype.options.length === 1 && ResolvedType.isUniqueType(oftype)) {
            return { chkexp: new TIRAsTypeExpression(sinfo, env.expressionResult, tiroftype), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
        else {
            return { chkexp: new TIRAsSubTypeExpression(sinfo, env.expressionResult, tiroftype), tenvs: renvs.tenvs, fenvs: renvs.fenvs };
        }
    }

    private processTypeAs(sinfo: SourceInfo, env: ExpressionTypeEnvironment, oftype: ResolvedType): ExpressionTypeEnvironment {
        const splits = this.splitOnTypeCheckAs(sinfo, env, oftype);
        this.raiseErrorIf(sinfo, splits.tenvs.length === 0, `convert to type ${oftype.typeID} from ${this.envExpressionGetInferType(env).typeID} always fails`);

        return env.setResultExpressionInfo(splits.chkexp, oftype, splits.tenvs);
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

    splitTypes(oft: ResolvedType, witht: ResolvedType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
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
        else {
            return undefined;
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
            const ttype = this.normalizeUnionList(ttypes);
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
    getSpecialTaskIDType(): ResolvedType { return this.internSpecialPrimitiveObjectType("TaskID"); }

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

    //When resolving a member on an task we must find a unique decl and implementation
    //const/function lookups will assert that an implementation was found
    resolveMemberFromTaskAtom<T extends OOMemberDecl> (sinfo: SourceInfo, ttype: ResolvedType, atom: ResolvedTaskAtomType, name: string, fnlookup: (tt: OOPTypeDecl) => T | undefined): OOMemberResolution<T> | ResolveResultFlag {
        //decls
        const decls = this.tryGetMemberDecls_helper(name, ResolvedType.createSingle(atom), atom.task, atom.binds, fnlookup);
        
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
        const impls = this.tryGetMemberImpl_helper(ResolvedType.createSingle(atom), atom.task, atom.binds, fnlookup);

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
            else if(atom instanceof ResolvedTaskAtomType) {
                return this.resolveMemberFromTaskAtom(sinfo, ResolvedType.createSingle(atom), atom, name, fnlookup);
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

    resolveMemberField(sinfo: SourceInfo, ttype: ResolvedType, name: string): OOMemberLookupInfo<MemberFieldDecl> | undefined {
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

    resolveMemberMethod(sinfo: SourceInfo, ttype: ResolvedType, name: string): OOMemberResolution<MemberMethodDecl> | undefined {
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

        this.raiseErrorIf(sinfo, !this.subtypeOf(this.envExpressionGetInferType(env), trgttype), `Cannot convert type ${this.envExpressionGetInferType(env)} into ${trgttype.typeID}`);
        return this.setResultExpressionBoolPassThrough(env, new TIRCoerceSafeExpression(sinfo, env.expressionResult, this.toTIRTypeKey(trgttype)), trgttype);
    }

    private emitSafeCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        return this.setResultExpressionBoolPassThrough(env, new TIRCoerceSafeExpression(sinfo, env.expressionResult, this.toTIRTypeKey(trgttype)), trgttype);
    }

    private emitCoerceToInferTypeIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo): ExpressionTypeEnvironment {
        const trgttype = this.envExpressionGetInferType(env);
        return this.emitSafeCoerceIfNeeded(env, sinfo, trgttype);
    }

    private emitRefCallCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        this.raiseErrorIf(sinfo, !this.subtypeOf(this.envExpressionGetInferType(env), trgttype), `Cannot convert type ${this.envExpressionGetInferType(env)} into ${trgttype.typeID}`);
        return this.setResultExpression(env, new TIRCoerceSafeRefCallResultExpression(sinfo, env.expressionResult, this.toTIRTypeKey(trgttype)), trgttype);
    }

    private emitTaskRefCallCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        this.raiseErrorIf(sinfo, !this.subtypeOf(this.envExpressionGetInferType(env), trgttype), `Cannot convert type ${this.envExpressionGetInferType(env)} into ${trgttype.typeID}`);
        return this.setResultExpression(env, new TIRCoerceSafeTaskRefCallResultExpression(sinfo, env.expressionResult, this.toTIRTypeKey(trgttype)), trgttype);
    }

    private emitActionCallCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        this.raiseErrorIf(sinfo, !this.subtypeOf(this.envExpressionGetInferType(env), trgttype), `Cannot convert type ${this.envExpressionGetInferType(env)} into ${trgttype.typeID}`);
        return this.setResultExpression(env, new TIRCoerceSafeActionCallResultExpression(sinfo, env.expressionResult, this.toTIRTypeKey(trgttype)), trgttype);
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

    private checkValueEq(lhsexp: Expression, lhs: ResolvedType, rhsexp: Expression, rhs: ResolvedType): "err" | "truealways" | "falsealways" | "lhsnone" | "rhsnone" | "lhsnothing" | "rhsnothing" | "lhssomekey" | "rhssomekey" | "lhssomekeywithunique" | "rhssomekeywithunique" | "stdkey" | "stdkeywithunique" {
        if (lhsexp instanceof LiteralNoneExpression && rhsexp instanceof LiteralNoneExpression) {
            return "truealways";
        }

        if (lhsexp instanceof LiteralNothingExpression && rhsexp instanceof LiteralNothingExpression) {
            return "truealways";
        }

        if (lhsexp instanceof LiteralNoneExpression) {
            return this.subtypeOf(this.getSpecialNoneType(), rhs) ? "lhsnone" : "falsealways";
        }

        if (rhsexp instanceof LiteralNoneExpression) {
            return this.subtypeOf(this.getSpecialNoneType(), lhs) ? "rhsnone" : "falsealways";
        }

        if (lhsexp instanceof LiteralNothingExpression) {
            return this.subtypeOf(this.getSpecialNothingType(), rhs) ? "lhsnothing" : "falsealways";
        }

        if (rhsexp instanceof LiteralNothingExpression) {
            return this.subtypeOf(this.getSpecialNothingType(), lhs) ? "rhsnothing" : "falsealways";
        }

        //should be a subtype on one of the sides
        if (!this.subtypeOf(lhs, rhs) && !this.subtypeOf(rhs, lhs)) {
            return "err";
        }

        if (lhs.typeID === rhs.typeID) {
            if(ResolvedType.isUniqueType(lhs) && ResolvedType.isUniqueType(rhs)) { 
                return "stdkeywithunique";
            }
            else {
                return "stdkey"
            }
        }
        else {
            if(this.subtypeOf(lhs, rhs)) {
                if(ResolvedType.isUniqueType(lhs)) {
                    return "lhssomekeywithunique";
                }
                else {
                    return "lhssomekey";
                }
            }
            else {
                if(ResolvedType.isUniqueType(rhs)) {
                    return "rhssomekeywithunique";
                }
                else {
                    return "rhssomekey";
                }
            }
        }
    }

    /*
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
                return this.checkExpression(env, arg, undefined);
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
        return  this.setResultExpression(env, new TIRLiteralNoneExpression(exp.sinfo), this.getSpecialNoneType());
    }

    private checkLiteralNothingExpression(env: ExpressionTypeEnvironment, exp: LiteralNothingExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralNothingExpression(exp.sinfo), this.getSpecialNothingType());
    }

    private checkLiteralBoolExpression(env: ExpressionTypeEnvironment, exp: LiteralBoolExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralBoolExpression(exp.sinfo, exp.value), this.getSpecialBoolType(), exp.value ? FlowTypeTruthValue.True : FlowTypeTruthValue.False);
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

        return this.setResultExpression(env, new TIRLiteralIntegralExpression(exp.sinfo, exp.value, this.toTIRTypeKey(itype)), itype);
    }

    private checkLiteralRationalExpression(env: ExpressionTypeEnvironment, exp: LiteralRationalExpression): ExpressionTypeEnvironment {
        //TODO: range check here
        return this.setResultExpression(env, new TIRLiteralRationalExpression(exp.sinfo, exp.value), this.getSpecialRationalType());
    } 

    private checkLiteralFloatExpression(env: ExpressionTypeEnvironment, exp: LiteralFloatPointExpression): ExpressionTypeEnvironment {
        const fptype = this.normalizeTypeOnly(exp.fptype, env.binds);

        //TODO: range check here
        return this.setResultExpression(env, new TIRLiteralFloatPointExpression(exp.sinfo, exp.value, this.toTIRTypeKey(fptype)), fptype);
    }

    private checkLiteralStringExpression(env: ExpressionTypeEnvironment, exp: LiteralStringExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralStringExpression(exp.sinfo, exp.value), this.getSpecialStringType());
    }

    private checkLiteralASCIIStringExpression(env: ExpressionTypeEnvironment, exp: LiteralASCIIStringExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralASCIIStringExpression(exp.sinfo, exp.value), this.getSpecialASCIIStringType());
     }

    private checkLiteralRegexExpression(env: ExpressionTypeEnvironment, exp: LiteralRegexExpression): ExpressionTypeEnvironment {
        return this.setResultExpression(env, new TIRLiteralRegexExpression(exp.sinfo, exp.value), this.getSpecialRegexType());
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

        return this.setResultExpression(env, new TIRLiteralTypedStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(stype), this.toTIRTypeKey(toftype)), stype);
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

        return this.setResultExpression(env, new TIRLiteralASCIITypedStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(stype), this.toTIRTypeKey(toftype)), stype);
    }

    private checkLiteralTemplateStringExpression(env: ExpressionTypeEnvironment, exp: LiteralTemplateStringExpression): ExpressionTypeEnvironment {
        //
        //TODO: maybe generate special TemplateString<T, K> ... types for these later -- right now we just expect them to be compile inlined
        //
        return this.setResultExpression(env, new TIRLiteralTemplateStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(this.getSpecialStringType())), this.getSpecialStringType());
    }

    private checkLiteralASCIITemplateStringExpression(env: ExpressionTypeEnvironment, exp: LiteralASCIITemplateStringExpression): ExpressionTypeEnvironment {
        //
        //TODO: maybe generate special TemplateString<T, K> ... types for these later -- right now we just expect them to be compile inlined
        //
        return this.setResultExpression(env, new TIRLiteralASCIITemplateStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(this.getSpecialASCIIStringType())), this.getSpecialASCIIStringType());
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
            return this.setResultExpression(env, nexp, constype);
        }
        else {
            const nexp = new TIRLiteralTypedPrimitiveConstructorExpression(exp.sinfo, (lexp[0] as TIRLiteralValue).exp, this.toTIRTypeKey(constype), this.toTIRTypeKey(ResolvedType.createSingle(ccdecl.representation)));
            return this.setResultExpression(env, nexp, constype);
        }
    }

    private checkAccessFormatInfo(env: ExpressionTypeEnvironment, exp: AccessFormatInfoExpression): ExpressionTypeEnvironment {
        assert(false, "TODO: maybe this is ok for string formats but right now this shouldn't happen");

        return env;
    }

    private checkAccessEnvValue(env: ExpressionTypeEnvironment, exp: AccessEnvValueExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk, `Can only access "environment" variables in task actions`);

        const valtype = this.normalizeTypeOnly(exp.valtype, env.binds);
        const restype = this.normalizeTypeOnly(new UnionTypeSignature(exp.sinfo, [exp.valtype, new NominalTypeSignature(exp.sinfo, "Core", ["None"])]), env.binds);

        return this.setResultExpression(env, new TIRAccessEnvValueExpression(exp.sinfo, exp.keyname, this.toTIRTypeKey(valtype), this.toTIRTypeKey(restype), exp.orNoneMode), restype);
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
            return this.setResultExpression(env, new TIRAccessNamespaceConstantExpression(exp.sinfo, nskey, nname, tirrtype), rtype);
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
            return this.setResultExpression(env, new TIRAccessConstMemberFieldExpression(exp.sinfo, sfkey, sfname, tirrtype), rtype);
        }
    }

    private checkAccessVariable(env: ExpressionTypeEnvironment, exp: AccessVariableExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);

        const vinfo = env.lookupVar(exp.name) as VarInfo;
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not have been assigned a value");

        return this.setResultExpression(env, new TIRAccessVariableExpression(exp.sinfo, exp.name, this.toTIRTypeKey(vinfo.declaredType)), vinfo.declaredType);
    }

    private checkConstructorPrimary(env: ExpressionTypeEnvironment, exp: ConstructorPrimaryExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.ctype, env.binds).tryGetUniqueEntityTypeInfo();
        this.raiseErrorIf(exp.sinfo, oftype === undefined, "Invalid constructor type");

        if(oftype instanceof ResolvedObjectEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            const allf = [...this.getAllOOFields(roftype, oftype.object, oftype.binds)];
            this.raiseErrorIf(exp.sinfo, allf.length !== exp.args.length, `got ${exp.args.length} args for constructor but expected ${allf.length}`);
            const eargs = exp.args.map((arg, i) => {
                const itype = this.normalizeTypeOnly(allf[i][1][2].declaredType, TemplateBindScope.createBaseBindScope(allf[i][1][3]));
                const ee = this.checkExpression(env, arg, itype);

                return this.emitCoerceIfNeeded(ee, exp.sinfo, itype);
            });

            if(!this.entityTypeConstructorHasInvariants(roftype, oftype.object, oftype.binds)) {
                const econs = new TIRConstructorPrimaryDirectExpression(exp.sinfo, tiroftype, eargs.map((earg) => earg.expressionResult));
                return this.setResultExpression(env, econs, roftype);
            }
            else {
                const econs = new TIRConstructorPrimaryCheckExpression(exp.sinfo, tiroftype, eargs.map((earg) => earg.expressionResult));
                return this.setResultExpression(env, econs, roftype);
            }
        }
        else if(oftype instanceof ResolvedTypedeclEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);

            this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, `${oftype.typeID} constructor expects a single arg`);
            const cexp = this.checkExpression(env, exp.args[0], ResolvedType.createSingle(oftype.valuetype));
            const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, ResolvedType.createSingle(oftype.valuetype));

            if (!this.typedeclTypeConstructorFromValueHasInvariants(roftype, oftype.object)) {
                const nexp = new TIRTypedeclDirectExpression(exp.sinfo, this.toTIRTypeKey(roftype), ecast.expressionResult);
                return this.setResultExpression(env, nexp, roftype);
            }
            else {
                const nexp = new TIRTypedeclConstructorExpression(exp.sinfo, this.toTIRTypeKey(roftype), ecast.expressionResult);
                return this.setResultExpression(env, nexp, roftype);
            }
        }
        else if(oftype instanceof ResolvedConstructableEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            if(oftype instanceof ResolvedOkEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Result<T, E>::Ok constructor expects a single arg of type T");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeT);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeT);

                return this.setResultExpression(env, new TIRResultOkConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedErrEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Result<T, E>::Ok constructor expects a single arg of type E");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeE);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeE);

                return this.setResultExpression(env, new TIRResultErrConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedSomethingEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Something<T> constructor expects a single arg of type T");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeT);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeT);

                return this.setResultExpression(env, new TIRSomethingConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedMapEntityAtomType) {
                const tirktype = this.toTIRTypeKey(oftype.typeK);
                const tirvtype = this.toTIRTypeKey(oftype.typeV);

                this.raiseErrorIf(exp.sinfo, exp.args.length !== 2, "MapEntry<K, V> constructor expects two args of type K, V");
                const kexp = this.checkExpression(env, exp.args[0], oftype.typeK);
                const vexp = this.checkExpression(env, exp.args[1], oftype.typeV);

                const kcast = this.emitCoerceIfNeeded(kexp, exp.args[0].sinfo, oftype.typeK);
                const vcast = this.emitCoerceIfNeeded(vexp, exp.args[1].sinfo, oftype.typeV);

                return this.setResultExpression(env, new TIRMapEntryConstructorExpression(exp.sinfo, kcast.expressionResult, vcast.expressionResult, tirktype, tirvtype, tiroftype), ResolvedType.createSingle(oftype));
            }
            else {
                this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${oftype.typeID}`);
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
        }
        else if (oftype instanceof ResolvedPrimitiveCollectionEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            if(oftype instanceof ResolvedListEntityAtomType) {
                const eargs = exp.args.map((arg) => {
                    const texp = this.checkExpression(env, arg, oftype.typeT);
                    return this.emitCoerceIfNeeded(texp, exp.sinfo, oftype.typeT);
                });

                return this.setResultExpression(env, new TIRConstructorListExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
            }
            else if(oftype instanceof ResolvedStackEntityAtomType) {
                this.raiseError(exp.sinfo, "Stack<T> not fully supported yet");
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedQueueEntityAtomType) {
                this.raiseError(exp.sinfo, "Queue<T> not fully supported yet");
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedSetEntityAtomType) {
                this.raiseError(exp.sinfo, "Set<T> not fully supported yet");
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedMapEntityAtomType) {
                const metype = this.normalizeTypeOnly(new NominalTypeSignature(exp.sinfo, "Core", ["MapEntry"], [new TemplateTypeSignature(exp.sinfo, "K"), new TemplateTypeSignature(exp.sinfo, "V")]), TemplateBindScope.createDoubleBindScope("K", oftype.typeK, "V", oftype.typeV));
                
                const eargs = exp.args.map((arg) => {
                    const texp = this.checkExpression(env, arg, metype);
                    return this.emitCoerceIfNeeded(texp, exp.sinfo, metype);
                });

                return this.setResultExpression(env, new TIRConstructorMapExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
            }
            else {
                this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${oftype.typeID}`);
                return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
        }
        else {
            this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${exp.ctype.getDiagnosticName()}`);
            return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, "None"), ResolvedType.createInvalid());
        }
    }

    private checkTupleConstructor(env: ExpressionTypeEnvironment, exp: ConstructorTupleExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedTupleAtomType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedTupleAtomType && desiredtype.options[0].types.length === exp.args.length) {
            itype = desiredtype.options[0]
        }

        if(itype === undefined) {
            const eargs = exp.args.map((arg) => this.checkExpression(env, arg, undefined));

            const roftype = ResolvedType.createSingle(ResolvedTupleAtomType.create(eargs.map((ee) => this.envExpressionGetInferType(ee))));
            const tiroftype = this.toTIRTypeKey(roftype);

            const cargs = eargs.map((arg) => this.emitCoerceToInferTypeIfNeeded(arg, exp.sinfo));
            return this.setResultExpression(env, new TIRConstructorTupleExpression(exp.sinfo, tiroftype, cargs.map((arg) => arg.expressionResult)), roftype);
        }
        else {
            const topts = itype.types;
            const eargs = exp.args.map((arg, i) => {
                const texp = this.checkExpression(env, arg, topts[i]);
                return this.emitCoerceIfNeeded(texp, exp.sinfo, topts[i]);
            });
        
            const roftype = ResolvedType.createSingle(itype);
            const tiroftype = this.toTIRTypeKey(roftype);

            return this.setResultExpression(env, new TIRConstructorTupleExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
        }
    }

    private checkRecordConstructor(env: ExpressionTypeEnvironment, exp: ConstructorRecordExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedRecordAtomType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedRecordAtomType && desiredtype.options[0].entries.length === exp.args.length) {
            itype = desiredtype.options[0]
        }

        if(itype === undefined) {
            const eargs = exp.args.map((arg) => {
                const cc = this.checkExpression(env, arg.value, undefined);
                return {pname: arg.property, penv: cc};
            });

            const roftype = ResolvedType.createSingle(ResolvedRecordAtomType.create(eargs.map((ee) => {
                return {pname: ee.pname, ptype: this.envExpressionGetInferType(ee.penv)};
            })));
            const tiroftype = this.toTIRTypeKey(roftype);

            const cargs = eargs.map((arg) => this.emitCoerceToInferTypeIfNeeded(arg.penv, exp.sinfo));
            return this.setResultExpression(env, new TIRConstructorRecordExpression(exp.sinfo, tiroftype, cargs.map((arg) => arg.expressionResult)), roftype);
        }
        else {
            const roftype = ResolvedType.createSingle(itype);
            const tiroftype = this.toTIRTypeKey(roftype);

            for(let i = 0; i < itype.entries.length; ++i) {
                if(itype.entries[i].pname !== exp.args[i].property) {
                    this.raiseError(exp.sinfo, `expected property name ${itype.entries[i].pname} but got ${exp.args[i].property}`);
                    return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, "None"), roftype);
                }
            }

            const topts = itype.entries;
            const eargs = exp.args.map((arg, i) => {
                const texp = this.checkExpression(env, arg.value, topts[i].ptype);
                return this.emitCoerceIfNeeded(texp, exp.sinfo, topts[i].ptype);
            });

            return this.setResultExpression(env, new TIRConstructorRecordExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
        }
    }

    private checkConstructorEphemeralValueList(env: ExpressionTypeEnvironment, exp: ConstructorEphemeralValueList, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedEphemeralListType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedEphemeralListType && desiredtype.options[0].types.length === exp.args.length) {
            itype = desiredtype.options[0]
        }

        if(itype === undefined) {
            const eargs = exp.args.map((arg) => this.checkExpression(env, arg, undefined));

            const roftype = ResolvedType.createSingle(ResolvedEphemeralListType.create(eargs.map((ee) => this.envExpressionGetInferType(ee))));
            const tiroftype = this.toTIRTypeKey(roftype);

            const cargs = eargs.map((arg) => this.emitCoerceToInferTypeIfNeeded(arg, exp.sinfo));
            return this.setResultExpression(env, new TIRConstructorEphemeralValueList(exp.sinfo, tiroftype, cargs.map((arg) => arg.expressionResult)), roftype);
        }
        else {
            const topts = itype.types;
            const eargs = exp.args.map((arg, i) => {
                const texp = this.checkExpression(env, arg, topts[i]);
                return this.emitCoerceIfNeeded(texp, exp.sinfo, topts[i]);
            });
        
            const roftype = ResolvedType.createSingle(itype);
            const tiroftype = this.toTIRTypeKey(roftype);

            return this.setResultExpression(env, new TIRConstructorEphemeralValueList(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
        }
    }

    private checkSpecialConstructorExpression(env: ExpressionTypeEnvironment, exp: SpecialConstructorExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        if(exp.rop === "something") {
            this.raiseErrorIf(exp.sinfo, desiredtype === undefined || (desiredtype.options.length !== 1 || !(desiredtype.typeID.startsWith("Option<"))), "something shorthand constructors only valid with Option typed expressions");
            const T = ((desiredtype as ResolvedType).options[0] as ResolvedConceptAtomType).getTBind();

            const cexp = this.checkExpression(env, exp.arg, T);
            const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, T);

            const roftype = this.getSomethingType(T);
            const tiroftype = this.toTIRTypeKey(roftype);

            const consenv = this.setResultExpression(ecast, new TIRSomethingConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype, undefined);
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
                const okenv = this.checkExpression(env, exp.arg, T);
                const tcast = this.emitCoerceIfNeeded(okenv, exp.sinfo, T);

                const rokconstype = this.getOkType(T, E);
                const tirokconstype = this.toTIRTypeKey(rokconstype);

                const consenv = this.setResultExpression(tcast, new TIRResultOkConstructorExpression(exp.sinfo, tirokconstype, tcast.expressionResult), rokconstype);
                return this.emitCoerceIfNeeded(consenv, exp.sinfo, desiredtype as ResolvedType);
            }
            else {
                const okenv = this.checkExpression(env, exp.arg, E);
                const tcast = this.emitCoerceIfNeeded(okenv, exp.sinfo, E);

                const rerrconstype = this.getOkType(T, E);
                const tirerrconstype = this.toTIRTypeKey(rerrconstype);

                const consenv = this.setResultExpression(tcast, new TIRResultErrConstructorExpression(exp.sinfo, tirerrconstype, tcast.expressionResult), rerrconstype);
                return this.emitCoerceIfNeeded(consenv, exp.sinfo, desiredtype as ResolvedType);
            }
        }
    }

    private checkPCodeInvokeExpression(env: ExpressionTypeEnvironment, exp: PCodeInvokeExpression): ExpressionTypeEnvironment {
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
            const argenv = this.checkExpression(env, exp.args[0], this.normalizeTypeOnly(exp.terms[0], env.binds));
            const astype = this.normalizeTypeOnly(exp.terms[1], env.binds);

            return this.emitSafeCoerceIfNeeded(argenv, exp.sinfo, astype);
        }
        else {
            if (nsdecl.operators.has(exp.name)) {
                const opsintro = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).find((nso) =>  nso.invoke.attributes.includes("abstract") || nso.invoke.attributes.includes("virtual"));
                const opdecls = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).filter((nso) => !nso.invoke.attributes.includes("abstract"));
                this.raiseErrorIf(exp.sinfo, opsintro !== undefined, "Operator must have exactly one abstract/virtual declaration");
                this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one implementation");

                const pnames = (opsintro as NamespaceOperatorDecl).invoke.params.map((p) => p.name);

                //No terms to be bound on operator call

                this.m_pendingNamespaceOperators.push({decl: opsintro as NamespaceOperatorDecl, impls: opdecls})

                const fkey = TIRInvokeIDGenerator.generateInvokeIDForNamespaceOperatorBase(nsdecl.ns, exp.name);
                const rtype = this.normalizeTypeOnly((opsintro as NamespaceOperatorDecl).invoke.resultType, TemplateBindScope.createEmptyBindScope());
                const tirrtype = this.toTIRTypeKey(rtype);

                const argexps = this.checkArgumentList(exp.sinfo, env, exp.args, (opsintro as NamespaceOperatorDecl).invoke.params.map((pp) => pp.type), TemplateBindScope.createEmptyBindScope());

                if(this.hasPreconditions((opsintro as NamespaceOperatorDecl).invoke) || this.hasPostconditions((opsintro as NamespaceOperatorDecl).invoke)) {
                    const tircall = new TIRCallNamespaceOperatorExpression(exp.sinfo, fkey, tirrtype, argexps);
                    return this.setResultExpression(env, tircall, rtype);
                }
                else {
                    const tircall = new TIRCallNamespaceOperatorWithChecksExpression(exp.sinfo, fkey, tirrtype, argexps);
                    return this.setResultExpression(env, tircall, rtype);
                }
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

                this.m_pendingNamespaceFunctions.push({decl: fdecl, binds: binds});

                const fkey = TIRInvokeIDGenerator.generateInvokeIDForNamespaceFunction(nsdecl.ns, exp.name, fdecl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
                const rtype = this.normalizeTypeOnly(fdecl.invoke.resultType, TemplateBindScope.createBaseBindScope(binds));
                const tirrtype = this.toTIRTypeKey(rtype);

                const argexps = this.checkArgumentList(exp.sinfo, env, exp.args, fdecl.invoke.params.map((pp) => pp.type), TemplateBindScope.createBaseBindScope(binds));

                if(this.hasPreconditions(fdecl.invoke) || this.hasPostconditions(fdecl.invoke)) {
                    const tircall = new TIRCallNamespaceFunctionExpression(exp.sinfo, fkey, tirrtype, argexps);
                    return this.setResultExpression(env, tircall, rtype);
                }
                else {
                    const tircall = new TIRCallNamespaceFunctionWithChecksExpression(exp.sinfo, fkey, tirrtype, argexps);
                    return this.setResultExpression(env, tircall, rtype);
                }
            }
        }
    }

    private checkCallStaticFunctionExpression(env: ExpressionTypeEnvironment, exp: CallStaticFunctionExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.ttype, env.binds);
        const tiroftype = this.toTIRTypeKey(oftype);

        const fdecltry = this.resolveMemberFunction(exp.sinfo, oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, (fdecltry === undefined), `Static function/operator not defined for type ${oftype.typeID}`);

        const fdecl = fdecltry as OOMemberLookupInfo<StaticFunctionDecl>;
        this.raiseErrorIf(exp.sinfo, fdecl.decl.invoke.terms.length !== exp.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for(let i = 0; i < fdecl.decl.invoke.terms.length; ++i) {
            binds.set(fdecl.decl.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], TemplateBindScope.createBaseBindScope(fdecl.oobinds)));
        }
        this.checkTemplateTypesOnInvoke(exp.sinfo, fdecl.decl.invoke.terms, TemplateBindScope.createBaseBindScope(fdecl.oobinds), binds, fdecl.decl.invoke.termRestrictions);

        const fdeclscope = TemplateBindScope.createBaseBindScope(fdecl.oobinds).pushScope(binds);
        const rtype = this.normalizeTypeOnly(fdecl.decl.invoke.resultType, fdeclscope);
        const tirrtype = this.toTIRTypeKey(rtype);

        if(oftype.typeID === "KeyType" && (exp.name === "less" || exp.name === "equal")) {
            const ktype = binds.get("K") as ResolvedType;
            this.raiseErrorIf(exp.sinfo, !this.subtypeOf(ktype, this.getSpecialKeyTypeConceptType()) || !ResolvedType.isGroundedType(ktype.options), "Invalid Key type argument");

            this.raiseErrorIf(exp.sinfo, exp.args.length !== 2, "expected 2 arguments");
            const lhsenv = this.checkExpression(env, exp.args[0], ktype);
            this.raiseErrorIf(exp.sinfo, !this.subtypeOf(this.envExpressionGetInferType(lhsenv), ktype), `expected arg of type ${ktype.typeID} but got ${this.envExpressionGetInferType(lhsenv).typeID}`);
            const rhsenv = this.checkExpression(env, exp.args[1], ktype);
            this.raiseErrorIf(exp.sinfo, !this.subtypeOf(this.envExpressionGetInferType(rhsenv), ktype), `expected arg of type ${ktype.typeID} but got ${this.envExpressionGetInferType(rhsenv).typeID}`);

            const tlhs = this.emitSafeCoerceIfNeeded(lhsenv, exp.sinfo, ktype);
            const trhs = this.emitSafeCoerceIfNeeded(rhsenv, exp.sinfo, ktype);

            if (exp.name === "equal") {
                if(ResolvedType.isUniqueType(ktype)) {
                    return this.setResultExpression(env, new TIRBinKeyEqBothUniqueExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
                else {
                    return this.setResultExpression(env, new TIRBinKeyEqGeneralExpression(exp.sinfo, this.toTIRTypeKey(ktype), tlhs.expressionResult, this.toTIRTypeKey(ktype), trhs.expressionResult), this.getSpecialBoolType());
                }
            }
            else {
                if(ResolvedType.isUniqueType(ktype)) {
                    return this.setResultExpression(env, new TIRBinKeyUniqueLessExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
                else {
                    return this.setResultExpression(env, new TIRBinKeyGeneralLessExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
            }
        }
        else if ((oftype.typeID === "String" || oftype.typeID === "ASCIIString") && exp.name === "interpolate") {
            this.raiseError(exp.sinfo, "interpolate is not implemented yet");
            return this.setResultExpression(env, new TIRInvalidExpression(exp.sinfo, tirrtype), rtype);
        }
        else {
            const argexps = this.checkArgumentList(exp.sinfo, env, exp.args, fdecl.decl.invoke.params.map((pp) => pp.type), fdeclscope);

            if (fdecl.decl.invoke.body !== undefined && fdecl.decl.invoke.body.body === "special_inject") {
                return this.setResultExpression(env, new TIRInjectExpression(exp.sinfo, argexps[0], tirrtype), rtype);
            }
            else {
                const fkey = TIRInvokeIDGenerator.generateInvokeForMemberFunction(tiroftype, exp.name, fdecl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
            
                this.m_pendingFunctionMemberDecls.push({decl: fdecl, binds: binds});

                if (this.hasPreconditions(fdecl.decl.invoke) || this.hasPostconditions(fdecl.decl.invoke)) {
                    const tircall = new TIRCallStaticFunctionExpression(exp.sinfo, fkey, tirrtype, argexps);
                    return this.setResultExpression(env, tircall, rtype);
                }
                else {
                    const tircall = new TIRCallStaticFunctionWithChecksExpression(exp.sinfo, fkey, tirrtype, argexps);
                    return this.setResultExpression(env, tircall, rtype);
                }
            }
        }
    }

    private checkLogicActionAndExpression(env: ExpressionTypeEnvironment, exp: LogicActionAndExpression): ExpressionTypeEnvironment {
        const bargs = exp.args.map((arg) => this.emitCoerceIfNeeded(this.checkExpression(env, arg, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType()));
        this.raiseErrorIf(exp.sinfo, bargs.some((ee) => this.envExpressionGetInferTruth(ee) === FlowTypeTruthValue.False), "Expression always evaluates to false");
        this.raiseErrorIf(exp.sinfo, bargs.every((ee) => this.envExpressionGetInferTruth(ee) === FlowTypeTruthValue.True), "Expression always evaluates to true");

        let tv = FlowTypeTruthValue.Unknown;
        if(bargs.some((ee) => this.envExpressionGetInferTruth(ee) === FlowTypeTruthValue.False)) {
            tv = FlowTypeTruthValue.False;
        }
        if(bargs.every((ee) => this.envExpressionGetInferTruth(ee) === FlowTypeTruthValue.True)) {
            tv = FlowTypeTruthValue.True;
        }

        //
        //TODO: we can split args here on truth value to make this flow sensitive too -- 1 option where they are all true + k options here each is individually false
        //
        return this.setResultExpression(env, new TIRLogicActionAndExpression(exp.sinfo, bargs.map((ee) => ee.expressionResult)), this.getSpecialBoolType(), tv);
    }

    private checkLogicActionOrExpression(env: ExpressionTypeEnvironment, exp: LogicActionOrExpression): ExpressionTypeEnvironment {
        const bargs = exp.args.map((arg) => this.emitCoerceIfNeeded(this.checkExpression(env, arg, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType()));
        this.raiseErrorIf(exp.sinfo, bargs.some((ee) => this.envExpressionGetInferTruth(ee) === FlowTypeTruthValue.True), "Expression always evaluates to true");
        this.raiseErrorIf(exp.sinfo, bargs.every((ee) => this.envExpressionGetInferTruth(ee) === FlowTypeTruthValue.False), "Expression always evaluates to false");

        let tv = FlowTypeTruthValue.Unknown;
        if(bargs.every((ee) => this.envExpressionGetInferTruth(ee) === FlowTypeTruthValue.False)) {
            tv = FlowTypeTruthValue.False;
        }
        if(bargs.some((ee) => this.envExpressionGetInferTruth(ee) === FlowTypeTruthValue.True)) {
            tv = FlowTypeTruthValue.True;
        }

        //
        //TODO: we can split args here on truth value to make this flow sensitive too -- 1 option where they are all true + k options here each is individually false
        //
        return this.setResultExpression(env, new TIRLogicActionOrExpression(exp.sinfo, bargs.map((ee) => ee.expressionResult)), this.getSpecialBoolType(), tv);
    }

    private checkAccessFromIndex(env: ExpressionTypeEnvironment, op: PostfixAccessFromIndex): ExpressionTypeEnvironment {
        this.raiseErrorIf(op.sinfo, !this.envExpressionGetInferType(env).options.some((atom) => !(atom instanceof ResolvedTupleAtomType)), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");
        this.raiseErrorIf(op.sinfo, this.envExpressionGetInferType(env).options.some((atom) => (atom as ResolvedTupleAtomType).types.length <= op.index), "Index may not be defined for tuple");

        this.raiseErrorIf(op.sinfo, this.envExpressionGetInferType(env).options.length !== 1, "only a single tuple is permitted -- todo: later want to generalize this")

        const idxtype = (this.envExpressionGetInferType(env).options[0] as ResolvedTupleAtomType).types[op.index];
        const tiridxtype = this.toTIRTypeKey(idxtype);

        return this.setResultExpression(env, new TIRLoadIndexExpression(op.sinfo, env.expressionResult, op.index, tiridxtype), idxtype);
    }

    private checkAccessFromName(env: ExpressionTypeEnvironment, op: PostfixAccessFromName): ExpressionTypeEnvironment {
        const isrecord = this.envExpressionGetInferType(env).options.every((atom) => atom instanceof TIRRecordType);
        const isobj = this.envExpressionGetInferType(env).options.every((atom) => atom instanceof ResolvedEntityAtomType);

        this.raiseErrorIf(op.sinfo, !isrecord && !isobj, `Cannot load the named location ${op.name} from type ${this.envExpressionGetInferType(env)}`);

        if (isrecord) {
            this.raiseErrorIf(op.sinfo, this.envExpressionGetInferType(env).options.some((atom) => (atom as ResolvedRecordAtomType).entries.find((entry) => entry.pname === op.name) === undefined), `Property "${op.name}" not be defined for record`);

            const rtype = ((this.envExpressionGetInferType(env).options[0] as ResolvedRecordAtomType).entries.find((entry) => entry.pname === op.name) as {pname: string, ptype: ResolvedType}).ptype;
            const tirrtype = this.toTIRTypeKey(rtype);

            return this.setResultExpression(env, new TIRLoadPropertyExpression(op.sinfo, env.expressionResult, op.name, tirrtype), rtype);
        }
        else {
            const fftry = this.resolveMemberField(op.sinfo, this.envExpressionGetInferType(env), op.name);
            this.raiseErrorIf(op.sinfo, fftry === undefined, `Could not resolve field "${op.name}" on type ${this.envExpressionGetInferType(env).typeID}`);
            const ff = fftry as OOMemberLookupInfo<MemberFieldDecl>;

            const fftype = this.normalizeTypeOnly(ff.decl.declaredType, TemplateBindScope.createBaseBindScope(ff.oobinds));
            const tirfftype = this.toTIRTypeKey(fftype);

            const fkey = TIRMemberIDGenerator.generateMemberFieldID(this.toTIRTypeKey(ff.ttype), op.name);

            if(ff.ootype instanceof EntityTypeDecl) {
                return this.setResultExpression(env, new TIRLoadFieldExpression(op.sinfo, env.expressionResult, fkey, tirfftype), fftype);
            }
            else {
                return this.setResultExpression(env, new TIRLoadFieldVirtualExpression(op.sinfo, env.expressionResult, fkey, tirfftype), fftype);
            }
        }
    }

    private checkPostfixIs(env: ExpressionTypeEnvironment, op: PostfixIs): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(op.istype, env.binds);
        return this.processTypeIs(op.sinfo, env, oftype);
    }

    private checkPostfixAs(env: ExpressionTypeEnvironment, op: PostfixAs): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(op.astype, env.binds);
        return this.processTypeAs(op.sinfo, env, oftype);
    }

    private checkInvoke(env: ExpressionTypeEnvironment, op: PostfixInvoke, refvar: string | undefined): ExpressionTypeEnvironment {
        const resolvefrom = op.specificResolve !== undefined ? this.normalizeTypeOnly(op.specificResolve, env.binds) : this.envExpressionGetInferType(env);
        const mresolvetry = this.resolveMemberMethod(op.sinfo, resolvefrom, op.name);

        this.raiseErrorIf(op.sinfo, op.isRefThis && refvar === undefined, "Cannot call a ref function in this expression position (top-level only)");

        this.raiseErrorIf(op.sinfo, mresolvetry === undefined, `Could not resolve method name "${op.name}" from type ${resolvefrom.typeID}`);
        const mresolve = mresolvetry as OOMemberResolution<MemberMethodDecl>;

        this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.terms.length !== op.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for (let i = 0; i < mresolve.decl.decl.invoke.terms.length; ++i) {
            binds.set(mresolve.decl.decl.invoke.terms[i].name, this.normalizeTypeOnly(op.terms[i], TemplateBindScope.createBaseBindScope(mresolve.decl.oobinds)));
        }
        this.checkTemplateTypesOnInvoke(op.sinfo, mresolve.decl.decl.invoke.terms, TemplateBindScope.createBaseBindScope(mresolve.decl.oobinds), binds, mresolve.decl.decl.invoke.termRestrictions);

        const fdeclscope = TemplateBindScope.createBaseBindScope(mresolve.decl.oobinds).pushScope(binds);
        const rtype = this.normalizeTypeOnly(mresolve.decl.decl.invoke.resultType, fdeclscope);
        const tirrtype = this.toTIRTypeKey(rtype);

        const tirdecltype = this.toTIRTypeKey(mresolve.decl.ttype);

        const argexps = this.checkArgumentList(op.sinfo, env.createFreshEnvExpressionFrom(), op.args, mresolve.decl.decl.invoke.params.map((pp) => pp.type), fdeclscope);

        if((!mresolve.decl.decl.attributes.includes("abstract") && !mresolve.decl.decl.attributes.includes("virtual"))) {
            this.raiseErrorIf(op.sinfo, mresolve.impl.length !== 1, `Could not resolve implementation for non-virtual method ${op.name} from ${resolvefrom.typeID}`);
            const knownimpl = mresolve.impl[0];

            if (knownimpl.decl.invoke.body !== undefined && (typeof (knownimpl.decl.invoke.body.body) === "string") && ["special_nothing", "special_something", "special_extract"].includes(knownimpl.decl.invoke.body.body as string)) {
                this.raiseErrorIf(op.sinfo, op.args.length !== 0, "No arguments permitted on this method");

                const sinv = knownimpl.decl.invoke.body.body as string;
                if (sinv === "special_nothing") {
                    return this.processTypeIs(op.sinfo, env, this.getSpecialNothingType());
                }
                else if (sinv === "special_something") {
                    return this.processTypeIs(op.sinfo, env, this.getSpecialISomethingConceptType());
                }
                else {
                    return this.setResultExpression(env, new TIRExtractExpression(op.sinfo, env.expressionResult, tirrtype), rtype);
                }
            }
            else {
                const fkey = TIRInvokeIDGenerator.generateInvokeForMemberMethod(tirdecltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
                this.m_pendingMethodMemberDecls.push({decl: knownimpl, binds: binds}, {decl: mresolve.decl, binds: binds});

                const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.impl[0].ttype);
                this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.isThisRef && !(mresolve.impl[0].ootype instanceof EntityTypeDecl), `self call with ref can only be done on non-virtual methods defined on entities but got ${mresolve.impl[0].ttype.typeID}`);

                if (this.hasPreconditions(mresolve.decl.decl.invoke) || this.hasPostconditions(mresolve.decl.decl.invoke)) {
                    if (mresolve.decl.decl.invoke.isThisRef) {
                        return this.setResultExpression(env, new TIRCallMemberFunctionSelfRefWithChecksExpression(op.sinfo, fkey, tirrtype, refvar as string, rcvrexp.expressionResult, argexps), rtype);
                    }
                    else {
                        return this.setResultExpression(env, new TIRCallMemberFunctionWithChecksExpression(op.sinfo, fkey, tirrtype, rcvrexp.expressionResult, argexps), rtype);
                    }
                }
                else {
                    if (mresolve.decl.decl.invoke.isThisRef) {
                        return this.setResultExpression(env, new TIRCallMemberFunctionSelfRefExpression(op.sinfo, fkey, tirrtype, refvar as string, rcvrexp.expressionResult, argexps), rtype);
                    }
                    else {
                        return this.setResultExpression(env, new TIRCallMemberFunctionExpression(op.sinfo, fkey, tirrtype, rcvrexp.expressionResult, argexps), rtype);
                    }
                }
            }
        }
        else {
            this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.isThisRef, "cannot use ref on virtual method call -- variance on updated this ref type")
            const declkey = TIRInvokeIDGenerator.generateInvokeForMemberMethod(tirdecltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
            this.m_pendingMethodMemberDecls.push({decl: mresolve.decl, binds: binds});

            const inferthistype = this.toTIRTypeKey(this.envExpressionGetInferType(env));
            let inferfkey: TIRInvokeKey | undefined = undefined;
            if(mresolve.impl.length === 1) {
                const tirimpltype = this.toTIRTypeKey(mresolve.impl[0].ttype);
                inferfkey = TIRInvokeIDGenerator.generateInvokeForMemberMethod(tirimpltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
                this.m_pendingMethodMemberDecls.push({decl: mresolve.impl[0], binds: binds});
            }

            const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.decl.ttype);
            if (this.hasPreconditions(mresolve.decl.decl.invoke) || this.hasPostconditions(mresolve.decl.decl.invoke)) {
                return this.setResultExpression(env, new TIRCallMemberFunctionDynamicWithChecksExpression(op.sinfo, declkey, inferthistype, inferfkey, tirrtype, rcvrexp.expressionResult, argexps), rtype);
            }
            else {
                return this.setResultExpression(env, new TIRCallMemberFunctionDynamicExpression(op.sinfo, declkey, inferthistype, inferfkey, tirrtype, rcvrexp.expressionResult, argexps), rtype);
            }
        }
    }

    private checkPostfixExpression(env: ExpressionTypeEnvironment, exp: PostfixOp, desiredtype: ResolvedType | undefined, refok: boolean): ExpressionTypeEnvironment {
        let cenv = this.checkExpression(env, exp.rootExp, undefined);

        let refvar: string | undefined = undefined;
        if(refok && (exp.rootExp instanceof AccessVariableExpression)) {
            refvar = exp.rootExp.name;
        }

        for (let i = 0; i < exp.ops.length; ++i) {
            //const lastop = (i + 1 === exp.ops.length);
            //const itype = lastop ? desiredtype : ((exp.ops[i + 1] instanceof PostfixAs) ? this.normalizeTypeOnly((exp.ops[i + 1] as PostfixAs).astype, cenv.binds) : undefined);

            switch (exp.ops[i].op) {
                case PostfixOpTag.PostfixAccessFromIndex: {
                    cenv = this.checkAccessFromIndex(cenv, exp.ops[i] as PostfixAccessFromIndex);
                    break;
                }
                case PostfixOpTag.PostfixAccessFromName: {
                    cenv = this.checkAccessFromName(cenv, exp.ops[i] as PostfixAccessFromName);
                    break;
                }
                case PostfixOpTag.PostfixIs: {
                    cenv = this.checkPostfixIs(cenv, exp.ops[i] as PostfixIs);
                    break;
                }
                case PostfixOpTag.PostfixAs: {
                    cenv = this.checkPostfixAs(cenv, exp.ops[i] as PostfixAs);
                    break;
                }
                default: {
                    this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== PostfixOpTag.PostfixInvoke, "Unknown postfix op");

                    cenv = this.checkInvoke(cenv, exp.ops[i] as PostfixInvoke, refvar);
                    break;
                }
            }

            //only want ref on first access
            refvar = undefined;
        }

        return cenv;
    }

    private checkPrefixNotOp(env: ExpressionTypeEnvironment, exp: PrefixNotOp): ExpressionTypeEnvironment {
        const benv = this.emitCoerceIfNeeded(this.checkExpression(env, exp.exp, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        return this.setResultExpressionBoolNegate(benv, new TIRPrefixNotOp(exp.sinfo, benv.expressionResult), this.getSpecialBoolType());
    }

    private checkPrefixNegateOpExpression(env: ExpressionTypeEnvironment, exp: PrefixNegateOp): ExpressionTypeEnvironment {
        const nenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env, exp.exp, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(nenv.trepr.options), `expected a numeric type but got ${nenv.trepr.typeID}`);

        const ntype = ResolvedType.getNumericBaseRepresentation(nenv.trepr.options);
        this.raiseErrorIf(exp.sinfo, ntype.typeID === "Nat" || ntype.typeID === "BigNat", `cannot negage unsigned type ${nenv.trepr.typeID}`);
        
        return this.setResultExpression(nenv, new TIRPrefixNegateOp(exp.sinfo, nenv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(ntype))), nenv.trepr)
    }

    private checkBinAddExpression(env: ExpressionTypeEnvironment, exp: BinAddExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `addition is defined on numeric values of same type but got -- ${lenv.trepr.typeID} + ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRBinAddExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), renv.trepr);
    }

    private checkBinSubExpression(env: ExpressionTypeEnvironment, exp: BinSubExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `subtraction is defined on numeric values of same type but got -- ${lenv.trepr.typeID} - ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRBinSubExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), renv.trepr);
    }

    private checkBinMultExpression(env: ExpressionTypeEnvironment, exp: BinMultExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        const lnt = ResolvedType.getNumericType(lenv.trepr.options);
        const lnb = ResolvedType.getNumericBaseRepresentation(lenv.trepr.options);

        const rnt = ResolvedType.getNumericType(renv.trepr.options);
        const rnb = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        this.raiseErrorIf(exp.sinfo, lnb.typeID !== rnb.typeID, `underlying numeric types must be compatible but got ${lnb.typeID} * ${rnb.typeID}`);

        if((lnt instanceof ResolvedPrimitiveInternalEntityAtomType) && (rnt instanceof ResolvedPrimitiveInternalEntityAtomType)) {
            return this.setResultExpression(env, new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
        }
        else {
            this.raiseErrorIf(exp.sinfo, (lnt instanceof ResolvedTypedeclEntityAtomType) && (rnt instanceof ResolvedTypedeclEntityAtomType), `multiplication requires at least on unit typed value but got ${lnt.typeID} * ${rnt.typeID}`);

            if(lnt instanceof ResolvedTypedeclEntityAtomType) {
                return this.setResultExpression(env, new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
            }
            else {
                return this.setResultExpression(env, new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(rnt));
            }
        }

        
        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `subtraction is defined on numeric values of same type but got -- ${lenv.trepr.typeID} - ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRBinSubExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), renv.trepr);
    }

    private checkBinDivExpression(env: ExpressionTypeEnvironment, exp: BinDivExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        const lnt = ResolvedType.getNumericType(lenv.trepr.options);
        const lnb = ResolvedType.getNumericBaseRepresentation(lenv.trepr.options);

        const rnt = ResolvedType.getNumericType(renv.trepr.options);
        const rnb = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        this.raiseErrorIf(exp.sinfo, lnb.typeID !== rnb.typeID, `underlying numeric types must be compatible but got ${lnb.typeID} / ${rnb.typeID}`);

        if((lnt instanceof ResolvedPrimitiveInternalEntityAtomType) && (rnt instanceof ResolvedPrimitiveInternalEntityAtomType)) {
            return this.setResultExpression(env, new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
        }
        else if((lnt instanceof ResolvedTypedeclEntityAtomType) && (rnt instanceof ResolvedTypedeclEntityAtomType)) {
            return this.setResultExpression(env, new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnb));
        }
        else {
            this.raiseErrorIf(exp.sinfo, !(rnt instanceof ResolvedPrimitiveInternalEntityAtomType), `division requires a typed number as numerator and a typed number or a unit type as divisor but got ${lnt.typeID} / ${rnt.typeID}`);

            return this.setResultExpression(env, new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
        }
    }

    private strongEQ(sinfo: SourceInfo, env: ExpressionTypeEnvironment, lhsarg: Expression, rhsarg: Expression): ExpressionTypeEnvironment {
        const lhsenv = this.checkExpression(env.createFreshEnvExpressionFrom(), lhsarg, undefined);
        const lhsinfertype = this.envExpressionGetInferType(lhsenv);
        const tirlhsinfertype = this.toTIRTypeKey(lhsinfertype);
        
        const rhsenv = this.checkExpression(env.createFreshEnvExpressionFrom(), rhsarg, undefined);
        const rhsinfertype = this.envExpressionGetInferType(rhsenv);
        const tirrhsinfertype = this.toTIRTypeKey(rhsinfertype);
        
        if (!this.subtypeOf(lhsinfertype, rhsinfertype) && !this.subtypeOf(rhsinfertype, lhsinfertype)) {
            this.raiseError(sinfo, `Types ${lhsinfertype.typeID} and ${rhsinfertype.typeID} are not comparable or comparision is always true/false`);
        }

        const action = this.checkValueEq(lhsarg, lhsinfertype, rhsarg, rhsinfertype);
        this.raiseErrorIf(sinfo, action === "err", "Types are not sufficiently overlapping");
        this.raiseErrorIf(sinfo, (action === "truealways" || action === "falsealways"), "equality operation is always true/false");
        
        if (action === "lhsnone") {
            return this.processTypeIs(sinfo, rhsenv, this.getSpecialNoneType());
        }
        else if (action === "rhsnone") {
            return this.processTypeIs(sinfo, lhsenv, this.getSpecialNoneType());
        }
        else if (action === "lhsnothing") {
            return this.processTypeIs(sinfo, rhsenv, this.getSpecialNothingType());
        }
        else if (action === "rhsnothing") {
            return this.processTypeIs(sinfo, lhsenv, this.getSpecialNothingType());
        }
        else {
            if (action === "stdkeywithunique") {
                this.raiseErrorIf(lhsarg.sinfo, this.subtypeOf(lhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${lhsinfertype.typeID}`);
                this.raiseErrorIf(rhsarg.sinfo, this.subtypeOf(rhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${rhsinfertype.typeID}`);

                const lhsunique = this.emitCoerceToInferTypeIfNeeded(lhsenv, lhsarg.sinfo);
                const rhsunique = this.emitCoerceToInferTypeIfNeeded(rhsenv, rhsarg.sinfo);
                const eqop = new TIRBinKeyEqBothUniqueExpression(sinfo, lhsunique.expressionResult, rhsunique.expressionResult, tirlhsinfertype);

                return this.setResultExpression(env, eqop, this.getSpecialBoolType());
            }
            else if (action === "lhssomekeywithunique") {
                this.raiseErrorIf(lhsarg.sinfo, this.subtypeOf(lhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${lhsinfertype.typeID}`);

                const eeunique = this.emitCoerceToInferTypeIfNeeded(lhsenv, lhsarg.sinfo);
                const eqop = new TIRBinKeyEqOneUniqueExpression(sinfo, tirlhsinfertype, eeunique.expressionResult, this.toTIRTypeKey(rhsenv.trepr), rhsenv.expressionResult);

                return this.processTypeIsFromEquality(sinfo, eqop, env, lhsinfertype);
            }
            else if (action === "rhssomekeywithunique") {
                this.raiseErrorIf(rhsarg.sinfo, this.subtypeOf(rhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${rhsinfertype.typeID}`);

                const eeunique = this.emitCoerceToInferTypeIfNeeded(rhsenv, rhsarg.sinfo);
                const eqop = new TIRBinKeyEqOneUniqueExpression(sinfo, tirrhsinfertype, eeunique.expressionResult, this.toTIRTypeKey(lhsenv.trepr), lhsenv.expressionResult);

                return this.processTypeIsFromEquality(sinfo, eqop, env, rhsinfertype);
            }
            else {
                const eqop = new TIRBinKeyEqGeneralExpression(sinfo, this.toTIRTypeKey(lhsenv.trepr), lhsenv.expressionResult, this.toTIRTypeKey(rhsenv.trepr), rhsenv.expressionResult);

                if (action === "lhssomekey") {
                    this.raiseErrorIf(lhsarg.sinfo, this.subtypeOf(lhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${lhsinfertype.typeID}`);

                    return this.processTypeIsFromEquality(sinfo, eqop, env, lhsinfertype);
                }
                else if (action === "rhssomekey") {
                    this.raiseErrorIf(rhsarg.sinfo, this.subtypeOf(rhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${rhsinfertype.typeID}`);

                    return this.processTypeIsFromEquality(sinfo, eqop, env, rhsinfertype);
                }
                else {
                    this.raiseErrorIf(lhsarg.sinfo, this.subtypeOf(lhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${lhsinfertype.typeID}`);
                    this.raiseErrorIf(rhsarg.sinfo, this.subtypeOf(rhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${rhsinfertype.typeID}`);

                    return this.setResultExpression(env, eqop, this.getSpecialBoolType());
                }
            }
        }
    }

    private strongNEQ(sinfo: SourceInfo, env: ExpressionTypeEnvironment, lhsarg: Expression, rhsarg: Expression): ExpressionTypeEnvironment {
        const lhsenv = this.checkExpression(env.createFreshEnvExpressionFrom(), lhsarg, undefined);
        const lhsinfertype = this.envExpressionGetInferType(lhsenv);
        const tirlhsinfertype = this.toTIRTypeKey(lhsinfertype);
        
        const rhsenv = this.checkExpression(env.createFreshEnvExpressionFrom(), rhsarg, undefined);
        const rhsinfertype = this.envExpressionGetInferType(rhsenv);
        const tirrhsinfertype = this.toTIRTypeKey(rhsinfertype);
        
        if (!this.subtypeOf(lhsinfertype, rhsinfertype) && !this.subtypeOf(rhsinfertype, lhsinfertype)) {
            this.raiseError(sinfo, `Types ${lhsinfertype.typeID} and ${rhsinfertype.typeID} are not comparable or comparision is always true/false`);
        }

        const action = this.checkValueEq(lhsarg, lhsinfertype, rhsarg, rhsinfertype);
        this.raiseErrorIf(sinfo, action === "err", "Types are not sufficiently overlapping");
        this.raiseErrorIf(sinfo, (action === "truealways" || action === "falsealways"), "equality operation is always true/false");

        if (action === "lhsnone") {
            return this.processTypeIsNot(sinfo, rhsenv, this.getSpecialSomeConceptType());
        }
        else if (action === "rhsnone") {
            return this.processTypeIsNot(sinfo, lhsenv, this.getSpecialNoneType());
        }
        else if (action === "lhsnothing") {
            return this.processTypeIsNot(sinfo, rhsenv, this.getSpecialNothingType());
        }
        else if (action === "rhsnothing") {
            return this.processTypeIsNot(sinfo, lhsenv, this.getSpecialNothingType());
        }
        else {
            if (action === "stdkeywithunique") {
                this.raiseErrorIf(lhsarg.sinfo, this.subtypeOf(lhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${lhsinfertype.typeID}`);
                this.raiseErrorIf(rhsarg.sinfo, this.subtypeOf(rhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${rhsinfertype.typeID}`);

                const lhsunique = this.emitCoerceToInferTypeIfNeeded(lhsenv, lhsarg.sinfo);
                const rhsunique = this.emitCoerceToInferTypeIfNeeded(rhsenv, rhsarg.sinfo);
                const eqop = new TIRBinKeyNeqBothUniqueExpression(sinfo, lhsunique.expressionResult, rhsunique.expressionResult, tirlhsinfertype);

                return this.setResultExpression(env, eqop, this.getSpecialBoolType());
            }
            else if (action === "lhssomekeywithunique") {
                this.raiseErrorIf(lhsarg.sinfo, this.subtypeOf(lhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${lhsinfertype.typeID}`);

                const eeunique = this.emitCoerceToInferTypeIfNeeded(lhsenv, lhsarg.sinfo);
                const eqop = new TIRBinKeyNeqOneUniqueExpression(sinfo, tirlhsinfertype, eeunique.expressionResult, this.toTIRTypeKey(rhsenv.trepr), rhsenv.expressionResult);

                return this.processTypeIsNotFromEquality(sinfo, eqop, env, lhsinfertype);
            }
            else if (action === "rhssomekeywithunique") {
                this.raiseErrorIf(rhsarg.sinfo, this.subtypeOf(rhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${rhsinfertype.typeID}`);

                const eeunique = this.emitCoerceToInferTypeIfNeeded(rhsenv, rhsarg.sinfo);
                const eqop = new TIRBinKeyNeqOneUniqueExpression(sinfo, tirrhsinfertype, eeunique.expressionResult, this.toTIRTypeKey(lhsenv.trepr), lhsenv.expressionResult);

                return this.processTypeIsNotFromEquality(sinfo, eqop, env, rhsinfertype);
            }
            else {
                const eqop = new TIRBinKeyNeqGeneralExpression(sinfo, this.toTIRTypeKey(lhsenv.trepr), lhsenv.expressionResult, this.toTIRTypeKey(rhsenv.trepr), rhsenv.expressionResult);

                if (action === "lhssomekey") {
                    this.raiseErrorIf(lhsarg.sinfo, this.subtypeOf(lhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${lhsinfertype.typeID}`);

                    return this.processTypeIsNotFromEquality(sinfo, eqop, env, lhsinfertype);
                }
                else if (action === "rhssomekey") {
                    this.raiseErrorIf(rhsarg.sinfo, this.subtypeOf(rhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${rhsinfertype.typeID}`);

                    return this.processTypeIsNotFromEquality(sinfo, eqop, env, rhsinfertype);
                }
                else {
                    this.raiseErrorIf(lhsarg.sinfo, this.subtypeOf(lhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${lhsinfertype.typeID}`);
                    this.raiseErrorIf(rhsarg.sinfo, this.subtypeOf(rhsinfertype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhsinfertype.options), `left hand side of compare expression -- expected a grounded KeyType but got ${rhsinfertype.typeID}`);

                    return this.setResultExpression(env, eqop, this.getSpecialBoolType());
                }
            }
        }
    }

    private checkNumericEqExpression(env: ExpressionTypeEnvironment, exp: NumericEqExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `equality is defined on numeric values of same type but got -- ${lenv.trepr.typeID} == ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRNumericEqExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericNeqExpression(env: ExpressionTypeEnvironment, exp: NumericNeqExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `equality is defined on numeric values of same type but got -- ${lenv.trepr.typeID} != ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRNumericNeqExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericLessExpression(env: ExpressionTypeEnvironment, exp: NumericLessExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `equality is defined on numeric values of same type but got -- ${lenv.trepr.typeID} < ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRNumericLessExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericLessEqExpression(env: ExpressionTypeEnvironment, exp: NumericLessEqExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `equality is defined on numeric values of same type but got -- ${lenv.trepr.typeID} <= ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRNumericLessEqExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericGreaterExpression(env: ExpressionTypeEnvironment, exp: NumericGreaterExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `equality is defined on numeric values of same type but got -- ${lenv.trepr.typeID} > ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRNumericGreaterExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericGreaterEqExpression(env: ExpressionTypeEnvironment, exp: NumericGreaterEqExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `equality is defined on numeric values of same type but got -- ${lenv.trepr.typeID} >= ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRNumericGreaterEqExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkBinLogicAnd(env: ExpressionTypeEnvironment, exp: BinLogicAndxpression): ExpressionTypeEnvironment {
        const lhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        this.raiseErrorIf(exp.lhs.sinfo, this.envExpressionGetInferTruth(lhs) !== FlowTypeTruthValue.Unknown, "Condition is always true/false");

        const lhsplits = this.convertToBoolFlowsOnResult(lhs);
        const ee = lhs.setResultExpressionInfo(new TIRInvalidExpression(exp.rhs.sinfo, this.toTIRTypeKey(this.getSpecialAnyConceptType())), ResolvedType.createInvalid(), lhsplits.tenvs);
        const rhs = this.emitCoerceIfNeeded(this.checkExpression(ee, exp.rhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        this.raiseErrorIf(exp.rhs.sinfo, this.envExpressionGetInferTruth(rhs) !== FlowTypeTruthValue.Unknown, "Condition is always true/false");

        const rhsplits = this.convertToBoolFlowsOnResult(rhs);

        const andexp = new TIRBinLogicAndxpression(exp.sinfo, lhs.expressionResult, rhs.expressionResult);
        const tflows = rhsplits.tenvs.map((tf) => tf.inferFlowInfo(andexp, this.getSpecialBoolType(), FlowTypeTruthValue.True));
        const fflows = [...lhsplits.fenvs, ...rhsplits.fenvs].map((tf) => tf.inferFlowInfo(andexp, this.getSpecialBoolType(), FlowTypeTruthValue.False));

        return env.setResultExpressionInfo(andexp, this.getSpecialBoolType(), this.envExpressionSimplifyFlowInfos([...tflows, ...fflows]));
    }

    private checkBinLogicOr(env: ExpressionTypeEnvironment, exp: BinLogicOrExpression): ExpressionTypeEnvironment {
        const lhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        this.raiseErrorIf(exp.lhs.sinfo, this.envExpressionGetInferTruth(lhs) !== FlowTypeTruthValue.Unknown, "Condition is always true/false");

        const lhsplits = this.convertToBoolFlowsOnResult(lhs);
        const ee = lhs.setResultExpressionInfo(new TIRInvalidExpression(exp.rhs.sinfo, this.toTIRTypeKey(this.getSpecialAnyConceptType())), ResolvedType.createInvalid(), lhsplits.fenvs);
        const rhs = this.emitCoerceIfNeeded(this.checkExpression(ee, exp.rhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        this.raiseErrorIf(exp.rhs.sinfo, this.envExpressionGetInferTruth(rhs) !== FlowTypeTruthValue.Unknown, "Condition is always true/false");

        const rhsplits = this.convertToBoolFlowsOnResult(rhs);

        const andexp = new TIRBinLogicOrExpression(exp.sinfo, lhs.expressionResult, rhs.expressionResult);
        const tflows = [...lhsplits.tenvs, ...rhsplits.tenvs].map((tf) => tf.inferFlowInfo(andexp, this.getSpecialBoolType(), FlowTypeTruthValue.True));
        const fflows = [...rhsplits.fenvs].map((tf) => tf.inferFlowInfo(andexp, this.getSpecialBoolType(), FlowTypeTruthValue.False));

        return env.setResultExpressionInfo(andexp, this.getSpecialBoolType(), this.envExpressionSimplifyFlowInfos([...tflows, ...fflows]));
    }

    private checkBinLogicImplies(env: ExpressionTypeEnvironment, exp: BinLogicImpliesExpression): ExpressionTypeEnvironment {
        const lhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        this.raiseErrorIf(exp.lhs.sinfo, this.envExpressionGetInferTruth(lhs) !== FlowTypeTruthValue.Unknown, "Condition is always true/false");

        const lhsplits = this.convertToBoolFlowsOnResult(lhs);
        const ee = lhs.setResultExpressionInfo(new TIRInvalidExpression(exp.rhs.sinfo, this.toTIRTypeKey(this.getSpecialAnyConceptType())), ResolvedType.createInvalid(), lhsplits.tenvs);
        const rhs = this.emitCoerceIfNeeded(this.checkExpression(ee, exp.rhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        this.raiseErrorIf(exp.rhs.sinfo, this.envExpressionGetInferTruth(rhs) !== FlowTypeTruthValue.Unknown, "Condition is always true/false");

        const rhsplits = this.convertToBoolFlowsOnResult(rhs);

        const andexp = new TIRBinLogicOrExpression(exp.sinfo, lhs.expressionResult, rhs.expressionResult);
        const tflows = [...lhsplits.fenvs, ...rhsplits.tenvs].map((tf) => tf.inferFlowInfo(andexp, this.getSpecialBoolType(), FlowTypeTruthValue.True));
        const fflows = [...rhsplits.tenvs].map((tf) => tf.inferFlowInfo(andexp, this.getSpecialBoolType(), FlowTypeTruthValue.False));

        return env.setResultExpressionInfo(andexp, this.getSpecialBoolType(), this.envExpressionSimplifyFlowInfos([...tflows, ...fflows]));
    }

    private checkMapEntryConstructorExpression(env: ExpressionTypeEnvironment, exp: MapEntryConstructorExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedMapEntityAtomType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedMapEntityAtomType) {
            itype = desiredtype.options[0]
        }

        const kenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.kexp, itype !== undefined ? itype.typeK : undefined);
        const venv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.vexp, itype !== undefined ? itype.typeV : undefined);

        this.raiseErrorIf(exp.kexp.sinfo, !this.subtypeOf(this.envExpressionGetInferType(kenv), this.getSpecialKeyTypeConceptType()) || !ResolvedType.isGroundedType(this.envExpressionGetInferType(kenv).options), "Key must be a grounded KeyType value");
        if(itype !== undefined) {
            const ktype = this.toTIRTypeKey(itype.typeK);
            const kexp = this.emitCoerceIfNeeded(kenv, exp.kexp.sinfo, itype.typeK);

            const vtype = this.toTIRTypeKey(itype.typeV);
            const vexp = this.emitCoerceIfNeeded(venv, exp.vexp.sinfo, itype.typeV);

            const medecl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("MapEntry") as EntityTypeDecl; 
            const metype = ResolvedType.createSingle(ResolvedMapEntryEntityAtomType.create(medecl, itype.typeK, itype.typeV));
            const oftype = this.toTIRTypeKey(metype);

            return this.setResultExpression(env, new TIRMapEntryConstructorExpression(exp.sinfo, kexp.expressionResult, vexp.expressionResult, ktype, vtype, oftype), metype);
        }
        else {
            const ktype = this.toTIRTypeKey(this.envExpressionGetInferType(kenv));
            const kexp = this.emitCoerceToInferTypeIfNeeded(kenv, exp.kexp.sinfo);

            const vtype = this.toTIRTypeKey(this.envExpressionGetInferType(venv));
            const vexp = this.emitCoerceToInferTypeIfNeeded(venv, exp.vexp.sinfo);

            const medecl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("MapEntry") as EntityTypeDecl; 
            const metype = ResolvedType.createSingle(ResolvedMapEntryEntityAtomType.create(medecl, this.envExpressionGetInferType(kenv), this.envExpressionGetInferType(venv)));
            const oftype = this.toTIRTypeKey(metype);

            return this.setResultExpression(env, new TIRMapEntryConstructorExpression(exp.sinfo, kexp.expressionResult, vexp.expressionResult, ktype, vtype, oftype), metype);
        }
    }

    private checkIfExpression(env: ExpressionTypeEnvironment, exp: IfExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let cenv = env;
        let results: {test: ExpressionTypeEnvironment, value: ExpressionTypeEnvironment}[] = [];

        for (let i = 0; i < exp.condflow.length; ++i) {
            const testenv = this.emitCoerceIfNeeded(this.checkExpression(cenv, exp.condflow[i].cond, undefined), exp.condflow[i].cond.sinfo, this.getSpecialBoolType());
            this.raiseErrorIf(exp.sinfo, this.envExpressionGetInferTruth(testenv) !== FlowTypeTruthValue.Unknown, "Test is always true/false");

            const cflow = this.convertToBoolFlowsOnResult(testenv);
            
            const trueenv = this.checkExpression(testenv.createFreshFlowEnvExpressionFrom(cflow.tenvs), exp.condflow[i].value, desiredtype);
            results.push({test: testenv, value: trueenv});
                
            cenv = testenv.createFreshFlowEnvExpressionFrom(cflow.fenvs);
        }
        const aenv = this.checkExpression(cenv, exp.elseflow, desiredtype);

        const iftype = this.normalizeUnionList(results.map((eev) => this.envExpressionGetInferType(eev.value)));
        
        const renv = env.createFreshFlowEnvExpressionFrom(this.envExpressionSimplifyFlowInfos(([] as FlowTypeInfoOption[]).concat(...results.map((ff) => ff.value.flowinfo))));
        const rexp = new TIRIfExpression(exp.sinfo, this.toTIRTypeKey(iftype), {test: results[0].test.expressionResult, value: this.emitSafeCoerceIfNeeded(results[0].value, results[0].value.expressionResult.sinfo, iftype).expressionResult}, results.slice(1).map((ffp) => {return {test: ffp.test.expressionResult, value: this.emitSafeCoerceIfNeeded(ffp.value, ffp.value.expressionResult.sinfo, iftype).expressionResult };}), this.emitSafeCoerceIfNeeded(aenv, exp.elseflow.sinfo, iftype).expressionResult);

        return this.setResultExpression(renv, rexp, iftype, FlowTypeTruthOps.join(...results.map((ff) => this.envExpressionGetInferTruth(ff.value))));
    }

    private checkSwitchExpression(env: ExpressionTypeEnvironment, exp: SwitchExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const venv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env, exp.sval, undefined), exp.sval.sinfo);
        
        let cenv: ExpressionTypeEnvironment = venv;
        let exhaustive = false;
        let results: {test: TIRLiteralValue | undefined, value: ExpressionTypeEnvironment}[] = [];
        for (let i = 0; i < exp.switchflow.length; ++i) {
            //it is a wildcard match
            if(exp.switchflow[i].condlit === undefined) {
                this.raiseErrorIf(exp.sinfo, i == exp.switchflow.length - 1, `wildcard should be last option in switch expression but there were ${exp.switchflow.length - (i + 1)} more that are unreachable`);

                const trueenv = this.checkExpression(cenv, exp.switchflow[i].value, desiredtype);

                results.push({test: undefined, value: trueenv});
                exhaustive = true;
                break;
            }
            else {
                const tvaltry = this.reduceLiteralValueToCanonicalForm("[SWITCH ENV]", (exp.switchflow[i].condlit as LiteralExpressionValue).exp, env.binds);
                this.raiseErrorIf((exp.switchflow[i].condlit as LiteralExpressionValue).exp.sinfo, tvaltry[0] === undefined, `could not resolve literal value`);
                const tval = tvaltry[0] as TIRLiteralValue;

                let fexp: ExpressionTypeEnvironment | undefined = undefined;
                if(tval.exp instanceof TIRLiteralNoneExpression) {
                    this.raiseErrorIf(tval.exp.sinfo, !this.subtypeOf(this.getSpecialNoneType(), this.envExpressionGetInferType(cenv)), `switch argument is never "none" so this case is never possible`);

                    if(this.envExpressionGetInferType(cenv).isNoneType()) {
                        this.raiseErrorIf(exp.sinfo, i == exp.switchflow.length - 1, `exhaustive none check should be last option in switch expression but there were ${exp.switchflow.length - (i + 1)} more that are unreachable`);

                        const trueenv = this.checkExpression(cenv, exp.switchflow[i].value, desiredtype);
                        results.push({test: undefined, value: trueenv});
                        exhaustive = true;
                        break;
                    }

                    fexp = this.processTypeIs(tval.exp.sinfo, cenv, this.getSpecialNoneType());
                }
                else if(tval.exp instanceof TIRLiteralNothingExpression) {
                    this.raiseErrorIf(tval.exp.sinfo, !this.subtypeOf(this.getSpecialNothingType(), this.envExpressionGetInferType(cenv)), `switch argument is never "nothing" so this case is never possible`);

                    if(this.envExpressionGetInferType(cenv).isNothingType()) {
                        this.raiseErrorIf(exp.sinfo, i == exp.switchflow.length - 1, `exhaustive nothing check should be last option in switch expression but there were ${exp.switchflow.length - (i + 1)} more that are unreachable`);

                        const trueenv = this.checkExpression(cenv, exp.switchflow[i].value, desiredtype);
                        results.push({test: undefined, value: trueenv});
                        exhaustive = true;
                        break;
                    }

                    fexp = this.processTypeIs(tval.exp.sinfo, cenv, this.getSpecialNothingType());
                }
                else {
                    this.raiseErrorIf(tval.exp.sinfo, !this.subtypeOf(tvaltry[1], this.envExpressionGetInferType(cenv)), `switch argument is never "${tvaltry[1].typeID}" so this case is never possible`);
                    
                    const eqop = new TIRBinKeyEqOneUniqueExpression(tval.exp.sinfo, tval.exp.etype, tval.exp, venv.expressionResult.etype, venv.expressionResult);
                    fexp = this.processTypeIsFromEquality(tval.exp.sinfo, eqop, cenv, tvaltry[1]);
                }
                const cflow = this.convertToBoolFlowsOnResult(fexp);

                const trueenv = this.checkExpression(fexp.createFreshFlowEnvExpressionFrom(cflow.tenvs), exp.switchflow[i].value, desiredtype);
                results.push({test: tval, value: trueenv});
                
                cenv = fexp.createFreshFlowEnvExpressionFrom(cflow.fenvs);
            }
        }

        const stype = this.normalizeUnionList(results.map((eev) => this.envExpressionGetInferType(eev.value)));
        const renv = venv.createFreshFlowEnvExpressionFrom(this.envExpressionSimplifyFlowInfos(([] as FlowTypeInfoOption[]).concat(...results.map((ff) => ff.value.flowinfo))));

        const clauses = results
            .filter((ffp) => ffp.test !== undefined)
            .map((ffp) => {
                return { match: ffp.test as TIRLiteralValue, value: this.emitSafeCoerceIfNeeded(ffp.value, ffp.value.expressionResult.sinfo, stype).expressionResult };
            });
        const edefault = results.find((ffp) => ffp.test === undefined) ? this.emitSafeCoerceIfNeeded(results[results.length - 1].value, exp.switchflow[exp.switchflow.length - 1].value.sinfo, stype).expressionResult : undefined;

        const rexp = new TIRSwitchExpression(exp.sinfo, this.toTIRTypeKey(stype), venv.expressionResult, clauses, edefault, exhaustive);
        return this.setResultExpression(renv, rexp, stype, FlowTypeTruthOps.join(...results.map((ff) => this.envExpressionGetInferTruth(ff.value))));
    }

    private checkMatchExpression(env: ExpressionTypeEnvironment, exp: MatchExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const venv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env, exp.sval, undefined), exp.sval.sinfo);
        
        let cenv: ExpressionTypeEnvironment = venv;
        let exhaustive = false;
        let results: {test: TIRExpression | undefined, ttype: TIRTypeKey | undefined, value: ExpressionTypeEnvironment}[] = [];
        for (let i = 0; i < exp.matchflow.length; ++i) {
            //it is a wildcard match
            if(exp.matchflow[i].mtype === undefined) {
                this.raiseErrorIf(exp.sinfo, i == exp.matchflow.length - 1, `wildcard should be last option in match expression but there were ${exp.matchflow.length - (i + 1)} more that are unreachable`);

                const trueenv = this.checkExpression(cenv, exp.matchflow[i].value, desiredtype);

                results.push({test: undefined, ttype: undefined, value: trueenv});
                exhaustive = true;
                break;
            }
            else {
                const testtype = this.normalizeTypeOnly(exp.matchflow[i].mtype as TypeSignature, env.binds);

                if(this.subtypeOf(this.envExpressionGetInferType(cenv), testtype)) {
                    this.raiseErrorIf(exp.sinfo, i == exp.matchflow.length - 1, `exhaustive none check should be last option in switch expression but there were ${exp.matchflow.length - (i + 1)} more that are unreachable`);

                    const trueenv = this.checkExpression(cenv, exp.matchflow[i].value, desiredtype);
                    results.push({test: undefined, ttype: undefined, value: trueenv});
                    exhaustive = true;
                    break;
                }
                else {
                    const fexp = this.processTypeIs((exp.matchflow[i].mtype as TypeSignature).sinfo, cenv, testtype);
                    const cflow = this.convertToBoolFlowsOnResult(fexp);

                    const trueenv = this.checkExpression(fexp.createFreshFlowEnvExpressionFrom(cflow.tenvs), exp.matchflow[i].value, desiredtype);
                    results.push({test: fexp.expressionResult, ttype: this.toTIRTypeKey(testtype), value: trueenv});
                
                    cenv = fexp.createFreshFlowEnvExpressionFrom(cflow.fenvs);
                }
            }
        }

        const stype = this.normalizeUnionList(results.map((eev) => this.envExpressionGetInferType(eev.value)));
        const renv = venv.createFreshFlowEnvExpressionFrom(this.envExpressionSimplifyFlowInfos(([] as FlowTypeInfoOption[]).concat(...results.map((ff) => ff.value.flowinfo))));

        const clauses = results
            .filter((ffp) => ffp.test !== undefined)
            .map((ffp) => {
                return { match: ffp.test as TIRExpression, mtype: ffp.ttype as TIRTypeKey, value: this.emitSafeCoerceIfNeeded(ffp.value, ffp.value.expressionResult.sinfo, stype).expressionResult };
            });
        const edefault = results.find((ffp) => ffp.test === undefined) ? this.emitSafeCoerceIfNeeded(results[results.length - 1].value, exp.matchflow[exp.matchflow.length - 1].value.sinfo, stype).expressionResult : undefined;

        const rexp = new TIRMatchExpression(exp.sinfo, this.toTIRTypeKey(stype), venv.expressionResult, clauses, edefault, exhaustive);
        return this.setResultExpression(renv, rexp, stype, FlowTypeTruthOps.join(...results.map((ff) => this.envExpressionGetInferTruth(ff.value))));
    }

    private checkTaskAccessField(env: ExpressionTypeEnvironment, exp: TaskSelfFieldExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        const fftry = tsk.taskdecl.memberFields.find((f) => f.name === exp.sfield);
        this.raiseErrorIf(exp.sinfo, fftry === undefined, `field ${exp.sfield} is not defined on task ${tsk.taskdecl.name}`);
        const ff = fftry as MemberFieldDecl;

        const fftype = this.normalizeTypeOnly(ff.declaredType, TemplateBindScope.createBaseBindScope(tsk.taskbinds));
        const tirfftype = this.toTIRTypeKey(fftype);

        const fkey = TIRMemberIDGenerator.generateMemberFieldID(this.toTIRTypeKey(tasktype), exp.sfield);
        return this.setResultExpression(env, new TIRTaskSelfFieldExpression(exp.sinfo, this.toTIRTypeKey(tasktype), fkey, exp.sfield, tirfftype), fftype);
    }

    private checkTaskSelfAction(env: ExpressionTypeEnvironment, exp: TaskSelfActionExpression, refop: boolean): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        const mresolvetry = tsk.taskdecl.memberMethods.find((mm) => mm.name === exp.name);
        this.raiseErrorIf(exp.sinfo, mresolvetry === undefined, `Could not resolve method name "${exp.name}" from type ${tasktype.typeID}`);
        const mresolve = mresolvetry as MemberMethodDecl;

        this.raiseErrorIf(exp.sinfo, refop !== mresolve.invoke.isThisRef, "Cannot call a action/ref function in this expression position");

        this.raiseErrorIf(exp.sinfo, mresolve.invoke.terms.length !== exp.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for (let i = 0; i < mresolve.invoke.terms.length; ++i) {
            binds.set(mresolve.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], TemplateBindScope.createBaseBindScope(tsk.taskbinds)));
        }
        this.checkTemplateTypesOnInvoke(exp.sinfo, mresolve.invoke.terms, TemplateBindScope.createBaseBindScope(tsk.taskbinds), binds, mresolve.invoke.termRestrictions);

        const fdeclscope = TemplateBindScope.createBaseBindScope(tsk.taskbinds).pushScope(binds);
        const rtype = this.normalizeTypeOnly(mresolve.invoke.resultType, fdeclscope);
        const tirrtype = this.toTIRTypeKey(rtype);

        const tirdecltype = this.toTIRTypeKey(tasktype);

        const argexps = this.checkArgumentList(exp.sinfo, env.createFreshEnvExpressionFrom(), exp.args, mresolve.invoke.params.map((pp) => pp.type), fdeclscope);

        const fkey = TIRInvokeIDGenerator.generateInvokeForMemberMethod(tirdecltype, exp.name, mresolve.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
        this.m_pendingMethodMemberDecls.push({decl: new OOMemberLookupInfo<MemberMethodDecl>(tasktype, tsk.taskdecl, tsk.taskbinds, mresolve), binds: binds});

        if(mresolve.invoke.attributes.includes("task_action")) {
            return this.setResultExpression(env, new TIRCallMemberActionExpression(exp.sinfo, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
        else if (mresolve.invoke.isThisRef) {
            return this.setResultExpression(env, new TIRCallMemberFunctionTaskSelfRefExpression(exp.sinfo, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
        else {
            return this.setResultExpression(env, new TIRCallMemberFunctionTaskExpression(exp.sinfo, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
    }

    private checkTaskGetIDExpression(env: ExpressionTypeEnvironment, exp: TaskGetIDExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        return this.setResultExpression(env, new TIRTaskGetIDExpression(exp.sinfo, this.toTIRTypeKey(tasktype),  this.toTIRTypeKey(this.getSpecialTaskIDType())), this.getSpecialTaskIDType());
    }

    private checkExpression(env: ExpressionTypeEnvironment, exp: Expression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression: {
                return this.checkLiteralNoneExpression(env, exp as LiteralNoneExpression);
            }
            case ExpressionTag.LiteralNothingExpression: {
                return this.checkLiteralNothingExpression(env, exp as LiteralNothingExpression);
            }
            case ExpressionTag.LiteralBoolExpression: { 
                return this.checkLiteralBoolExpression(env, exp as LiteralBoolExpression);
            }
            case ExpressionTag.LiteralIntegralExpression: {
                return this.checkLiteralIntegralExpression(env, exp as LiteralIntegralExpression);
            }
            case ExpressionTag.LiteralRationalExpression: {
                return this.checkLiteralRationalExpression(env, exp as LiteralRationalExpression);
            }
            case ExpressionTag.LiteralFloatPointExpression: {
                return this.checkLiteralFloatExpression(env, exp as LiteralFloatPointExpression);
            }
            case ExpressionTag.LiteralRegexExpression: {
                return this.checkLiteralRegexExpression(env, exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralStringExpression: { 
                return this.checkLiteralStringExpression(env, exp as LiteralStringExpression);
            }
            case ExpressionTag.LiteralASCIIStringExpression: { 
                return this.checkLiteralASCIIStringExpression(env, exp as LiteralStringExpression);
            }
            case ExpressionTag.LiteralTypedStringExpression: {
                return this.checkLiteralTypedStringExpression(env, exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralASCIITypedStringExpression: {
                return this.checkLiteralASCIITypedStringExpression(env, exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralTemplateStringExpression: {
                return this.checkLiteralTemplateStringExpression(env, exp as LiteralTemplateStringExpression);
            }
            case ExpressionTag.LiteralASCIITemplateStringExpression: {
                return this.checkLiteralASCIITemplateStringExpression(env, exp as LiteralTemplateStringExpression);
            }
            case ExpressionTag.LiteralTypedPrimitiveConstructorExpression: {
                return this.checkLiteralTypedPrimitiveConstructorExpression(env, exp as LiteralTypedPrimitiveConstructorExpression);
            }
            case ExpressionTag.AccessFormatInfoExpression: {
                return this.checkAccessFormatInfo(env, exp as AccessFormatInfoExpression);
            }
            case ExpressionTag.AccessEnvValueExpression: {
                return this.checkAccessEnvValue(env, exp as AccessEnvValueExpression);
            }
            case ExpressionTag.AccessNamespaceConstantExpression: {
                return this.checkAccessNamespaceConstant(env, exp as AccessNamespaceConstantExpression);
            }
            case ExpressionTag.AccessStaticFieldExpression: {
                return this.checkAccessStaticField(env, exp as AccessStaticFieldExpression);
            }
            case ExpressionTag.AccessVariableExpression: {
                return this.checkAccessVariable(env, exp as AccessVariableExpression);
            }
            case ExpressionTag.ConstructorPrimaryExpression: {
                return this.checkConstructorPrimary(env, exp as ConstructorPrimaryExpression);
            }
            case ExpressionTag.ConstructorTupleExpression: {
                return this.checkTupleConstructor(env, exp as ConstructorTupleExpression, desiredtype);
            }
            case ExpressionTag.ConstructorRecordExpression: {
                return this.checkRecordConstructor(env, exp as ConstructorRecordExpression, desiredtype);
            }
            case ExpressionTag.ConstructorEphemeralValueList: {
                return this.checkConstructorEphemeralValueList(env, exp as ConstructorEphemeralValueList, desiredtype);
            }
            //PCode constructor always handled in agrument processing -- can't just create them randomly
            case ExpressionTag.PCodeInvokeExpression: {
                return this.checkPCodeInvokeExpression(env, exp as PCodeInvokeExpression);
            }
            case ExpressionTag.SpecialConstructorExpression: {
                return this.checkSpecialConstructorExpression(env, exp as SpecialConstructorExpression, desiredtype);
            }
            case ExpressionTag.CallNamespaceFunctionOrOperatorExpression: {
                return this.checkCallNamespaceFunctionOrOperatorExpression(env, exp as CallNamespaceFunctionOrOperatorExpression);
            }
            case ExpressionTag.CallStaticFunctionExpression: {
                return this.checkCallStaticFunctionExpression(env, exp as CallStaticFunctionExpression);
            }
            case ExpressionTag.LogicActionAndExpression: {
                return this.checkLogicActionAndExpression(env, exp as LogicActionAndExpression);
            }
            case ExpressionTag.LogicActionOrExpression: {
                return this.checkLogicActionOrExpression(env, exp as LogicActionOrExpression);
            }
            case ExpressionTag.PostfixOpExpression: {
                return this.checkPostfixExpression(env, exp as PostfixOp, desiredtype, false)
            }
            case ExpressionTag.PrefixNotOpExpression: {
                return this.checkPrefixNotOp(env, exp as PrefixNotOp);
            }
            case ExpressionTag.PrefixNegateOpExpression: {
                return this.checkPrefixNegateOpExpression(env, exp as PrefixNegateOp);
            }
            case ExpressionTag.BinAddExpression: {
                return this.checkBinAddExpression(env, exp as BinAddExpression);
            }
            case ExpressionTag.BinSubExpression: {
                return this.checkBinSubExpression(env, exp as BinSubExpression);
            }
            case ExpressionTag.BinMultExpression: {
                return this.checkBinMultExpression(env, exp as BinMultExpression);
            }
            case ExpressionTag.BinDivExpression: {
                return this.checkBinDivExpression(env, exp as BinDivExpression);
            }
            case ExpressionTag.BinKeyEqExpression: {
                const bke = exp as BinKeyEqExpression;
                return this.strongEQ(exp.sinfo, env, bke.lhs, bke.rhs);
            }
            case ExpressionTag.BinKeyNeqExpression: {
                const bkne = exp as BinKeyNeqExpression;
                return this.strongNEQ(exp.sinfo, env, bkne.lhs, bkne.rhs);
            }
            case ExpressionTag.NumericEqExpression: {
                return this.checkNumericEqExpression(env, exp as NumericEqExpression);
            }
            case ExpressionTag.NumericNeqExpression: {
                return this.checkNumericNeqExpression(env, exp as NumericNeqExpression);
            }
            case ExpressionTag.NumericLessExpression: {
                return this.checkNumericLessExpression(env, exp as NumericLessExpression);
            }
            case ExpressionTag.NumericLessEqExpression: {
                return this.checkNumericLessEqExpression(env, exp as NumericLessEqExpression);
            }
            case ExpressionTag.NumericGreaterExpression: {
                return this.checkNumericGreaterExpression(env, exp as NumericGreaterExpression);
            }
            case ExpressionTag.NumericGreaterEqExpression: {
                return this.checkNumericGreaterEqExpression(env, exp as NumericGreaterEqExpression);
            }
            case ExpressionTag.BinLogicAndExpression: {
                return this.checkBinLogicAnd(env, exp as BinLogicAndxpression);
            }
            case ExpressionTag.BinLogicOrExpression: {
                return this.checkBinLogicOr(env, exp as BinLogicOrExpression);
            }
            case ExpressionTag.BinLogicImpliesExpression: {
                return this.checkBinLogicImplies(env, exp as BinLogicImpliesExpression);
            }
            case ExpressionTag.MapEntryConstructorExpression: {
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, desiredtype);
            }
            case ExpressionTag.IfExpression: {
                return this.checkIfExpression(env, exp as IfExpression, desiredtype);
            }
            case ExpressionTag.SwitchExpression: {
                return this.checkSwitchExpression(env, exp as SwitchExpression, desiredtype);
            }
            case ExpressionTag.MatchExpression: {
                return this.checkMatchExpression(env, exp as MatchExpression, desiredtype);
            }
            case ExpressionTag.TaskSelfFieldExpression: {
                return this.checkTaskAccessField(env, exp as TaskSelfFieldExpression);
            }
            case ExpressionTag.TaskSelfActionExpression: {
                return this.checkTaskSelfAction(env, exp as TaskSelfActionExpression, false);
            }
            case ExpressionTag.TaskGetIDExpression: {
                return this.checkTaskGetIDExpression(env, exp as TaskGetIDExpression);
            }
            default: {
                this.raiseError(exp.sinfo, `Unknown expression kind -- ${exp.tag}`);
                return env;
            }
        }
    }

    private checkExpressionAtAssign(env: ExpressionTypeEnvironment, exp: Expression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        switch (exp.tag) {
            case ExpressionTag.PostfixOpExpression: {
                return this.checkPostfixExpression(env, exp as PostfixOp, desiredtype, true)
            }
            case ExpressionTag.TaskSelfActionExpression: {
                return this.checkTaskSelfAction(env, exp as TaskSelfActionExpression, true);
            }
            default: {
                return this.checkExpression(env, exp, desiredtype);
            }
        }
    }

    private checkMultiExpressionAtAssign(env: ExpressionTypeEnvironment, exp: Expression[], desiredtype: (ResolvedType | undefined)[]): ExpressionTypeEnvironment[] {
        if (exp.length === 1) {
            //There is no need to try and enforce a desired type since the result is ephemeral list that we will restructure anyway
            //Right now this has to be a call expression -- which ignores the desired type info anyway

            return [this.checkExpressionAtAssign(env, exp[0], undefined)];
        }
        else {
            //here we want to try and coearce each expression individually

            return exp.map((ee, ii) => {
                switch (ee.tag) {
                    case ExpressionTag.PostfixOpExpression: {
                        return this.checkPostfixExpression(env.createFreshEnvExpressionFrom(), ee as PostfixOp, desiredtype[ii], true)
                    }
                    case ExpressionTag.TaskSelfActionExpression: {
                        return this.checkTaskSelfAction(env.createFreshEnvExpressionFrom(), ee as TaskSelfActionExpression, true);
                    }
                    default: {
                        return this.checkExpression(env.createFreshEnvExpressionFrom(), ee, desiredtype[ii]);
                    }
                }
            });
        }
    }

    private checkDeclareSingleVariableExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vname: string, isConst: boolean, decltype: TypeSignature, rhs: ExpressionTypeEnvironment | undefined): StatementTypeEnvironment {
        this.raiseErrorIf(sinfo, env.isVarNameDefined(vname), `${vname} cannot shadow previous definition`);

        const infertype = rhs !== undefined ? this.envExpressionGetInferType(rhs) : undefined;
        this.raiseErrorIf(sinfo, infertype === undefined && isConst, "must define const var at declaration site");
        this.raiseErrorIf(sinfo, infertype === undefined && decltype instanceof AutoTypeSignature, "must define auto typed var at declaration site");

        const vtype = (decltype instanceof AutoTypeSignature) ? infertype as ResolvedType : this.normalizeTypeOnly(decltype, env.binds);
        this.raiseErrorIf(sinfo, infertype !== undefined && !this.subtypeOf(infertype, vtype), `expression is not of declared type ${vtype.typeID}`);

        return env.addVar(vname, isConst, vtype, infertype !== undefined, rhs);
    }

    private checkDeclareMultipleVariableExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, isConst: boolean, vars: {vname: string, decltype: TypeSignature}[], rhs: ExpressionTypeEnvironment | undefined): StatementTypeEnvironment {
        const iitype = rhs !== undefined ? this.envExpressionGetInferType(rhs) : undefined;
        this.raiseErrorIf(sinfo, iitype !== undefined && iitype.options.length !== 1 && !(iitype.options[0] instanceof ResolvedEphemeralListType), `expected multiple assign values`);
        this.raiseErrorIf(sinfo, iitype !== undefined && (iitype.options[0] as ResolvedEphemeralListType).types.length < vars.length, `expected at least ${vars.length} values`);

        let cenv = env;
        for(let i = 0; i < vars.length; ++i) {
            this.raiseErrorIf(sinfo, env.isVarNameDefined(vars[i].vname), `${vars[i].vname} cannot shadow previous definition`);
    
            const infertype = iitype !== undefined ? (iitype.options[0] as ResolvedEphemeralListType).types[i] : undefined;
            this.raiseErrorIf(sinfo, infertype === undefined && isConst, "Must define const var at declaration site");
            this.raiseErrorIf(sinfo, infertype === undefined && vars[i].decltype instanceof AutoTypeSignature, "Must define auto typed var at declaration site");

            const vtype = (vars[i].decltype instanceof AutoTypeSignature) ? infertype as ResolvedType : this.normalizeTypeOnly(vars[i].decltype, env.binds);
            this.raiseErrorIf(sinfo, infertype !== undefined && !this.subtypeOf(infertype, vtype), `Expression is not of declared type ${vtype.typeID}`);

            cenv = env.addVar(vars[i].vname, isConst, vtype, infertype !== undefined, rhs);
        }

        return cenv;
    }

    private checkAssignSingleVariableExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vname: string, rhs: ExpressionTypeEnvironment): StatementTypeEnvironment {
        const vinfo = env.lookupVar(vname);
        this.raiseErrorIf(sinfo, vinfo === null, `Variable ${vname} was not previously defined`);
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, `Variable ${vname} is defined as const`);

        this.raiseErrorIf(sinfo, !this.subtypeOf(this.envExpressionGetInferType(rhs), (vinfo as VarInfo).declaredType), `Assign value (${this.envExpressionGetInferType(rhs).typeID}) is not subtype of declared variable type ${(vinfo as VarInfo).declaredType}`);

        return env.setVar(vname, rhs);
    }

    private checkAssignMultipleVariableExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vars: string[], rhs: ExpressionTypeEnvironment): StatementTypeEnvironment {
        const iitype = this.envExpressionGetInferType(rhs);
        this.raiseErrorIf(sinfo, iitype !== undefined && iitype.options.length !== 1 && !(iitype.options[0] instanceof ResolvedEphemeralListType), `expected multiple assign values`);
        this.raiseErrorIf(sinfo, iitype !== undefined && (iitype.options[0] as ResolvedEphemeralListType).types.length < vars.length, `expected at least ${vars.length} values`);

        let cenv = env;
        for (let i = 0; i < vars.length; ++i) {
            const vinfo = env.lookupVar(vars[i]);
            this.raiseErrorIf(sinfo, vinfo === null, `Variable ${vars[i]} was not previously defined`);
            this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, `Variable ${vars[i]} is defined as const`);

            this.raiseErrorIf(sinfo, !this.subtypeOf((iitype.options[0] as ResolvedEphemeralListType).types[i], (vinfo as VarInfo).declaredType), `Assign value (${(iitype.options[0] as ResolvedEphemeralListType).types[i].typeID}) is not subtype of declared variable type ${(vinfo as VarInfo).declaredType}`);

            cenv = env.setVar(vars[i], rhs);
        }

        return cenv;
    }
    
    private checkEmptyStatement(env: StatementTypeEnvironment, stmt: EmptyStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return [env, []];
    }

    private checkVariableDeclarationStatement(env: StatementTypeEnvironment, stmt: VariableDeclarationStatement): [StatementTypeEnvironment, TIRStatement[]] {
        if(stmt.exp === undefined) {
            const declenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, undefined);

            return [declenv, [new TIRVarDeclareStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey((declenv.lookupVar(stmt.name) as VarInfo).declaredType))]];
        }
        else {
            const itype = !(stmt.vtype instanceof AutoTypeSignature) ? this.normalizeTypeOnly(stmt.vtype, env.binds) : undefined;
            let rhs = this.checkExpressionAtAssign(env.createInitialEnvForExpressionEval(), stmt.exp, itype);

            let nstmt: TIRStatement[] = [];
            let nenv: StatementTypeEnvironment | undefined = undefined;
            if(rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, this.envClearExps(rhs, rhs.expressionResult.thisref));

                const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
                const refv = rhs.expressionResult.thisref;
                const rhsconv = this.emitRefCallCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

                nstmt = [new TIRVarDeclareAndAssignStatementWRef(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, stmt.isConst, refv)];
            }
            else if(rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefWithChecksExpression) {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, this.envClearExps(rhs, rhs.expressionResult.thisref));

                const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
                const refv = rhs.expressionResult.thisref;
                const rhsconv = this.emitRefCallCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

                nstmt = [new TIRVarDeclareAndAssignStatementWRef(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, stmt.isConst, refv)];
            }
            else if (rhs.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, this.envClearExps(rhs, "self"));

                const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
                const rhsconv = this.emitTaskRefCallCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

                nstmt = [new TIRVarDeclareAndAssignStatementWTaskRef(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, stmt.isConst, rhs.expressionResult.tsktype)];
            }
            else if (rhs.expressionResult instanceof TIRCallMemberActionExpression) {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, this.envClearExps(rhs, "self"));

                const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
                const rhsconv = this.emitActionCallCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

                nstmt = [new TIRVarDeclareAndAssignStatementWAction(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, stmt.isConst, rhs.expressionResult.tsktype)];
            }
            else {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, rhs);

                const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
                const rhsconv = this.emitCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

                nstmt = [new TIRVarDeclareAndAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, stmt.isConst)];
            }
            
            return [nenv, nstmt];
        }
    }

    private checkMultiReturnVariableDeclarationStatement(env: StatementTypeEnvironment, stmt: MultiReturnWithDeclarationStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const vvdecls = stmt.vars.map((vv) => {
            return {vname: vv.name, decltype: vv.vtype};
        });

        if(stmt.exp === undefined) {
            const declenv = this.checkDeclareMultipleVariableExplicit(stmt.sinfo, env, stmt.isConst, vvdecls, undefined);

            const tirdecls = stmt.vars.map((vv) => {
                const vtype = this.toTIRTypeKey((declenv.lookupVar(vv.name) as VarInfo).declaredType);
                return {vname: vv.name, vtype: vtype};
            });

            return [declenv, [new TIRMultiVarDeclareStatement(stmt.sinfo, tirdecls)]];
        }
        else {
            if(stmt.exp.length !== 1) {
                const itypes: (ResolvedType | undefined)[] = stmt.vars.map((vv) => {
                    return !(vv.vtype instanceof AutoTypeSignature) ? this.normalizeTypeOnly(vv.vtype, env.binds) : undefined;
                });
                const rhsexps = this.checkMultiExpressionAtAssign(env.createInitialEnvForExpressionEval(), stmt.exp, itypes);

                this.raiseErrorIf(stmt.sinfo, stmt.exp.length !== rhsexps.length, `mismatch between number of variables assigned and number of expressions`);
                
                const ielist = ResolvedType.createSingle(ResolvedEphemeralListType.create(stmt.vars.map((vv, ii) => !(vv.vtype instanceof AutoTypeSignature) ? this.normalizeTypeOnly(vv.vtype, env.binds) : this.envExpressionGetInferType(rhsexps[ii]))));
                const createpack = new TIRConstructorEphemeralValueList(stmt.sinfo, this.toTIRTypeKey(ielist), rhsexps.map((rr, ii) => this.emitCoerceIfNeeded(rr, rr.expressionResult.sinfo, (ielist.options[0] as ResolvedEphemeralListType).types[ii]).expressionResult));

                const vvinfo = stmt.vars.map((vv, ii) => {
                    return {vname: vv.name, pos: vv.pos, vtype: this.toTIRTypeKey((ielist.options[0] as ResolvedEphemeralListType).types[ii])};
                });

                const declenv = this.checkDeclareMultipleVariableExplicit(stmt.sinfo, env, stmt.isConst, vvdecls, this.setResultExpression(env.createInitialEnvForExpressionEval(), createpack, ielist, undefined));
                return [declenv, [new TIRMultiVarDeclareAndAssignStatement(stmt.sinfo, vvinfo, createpack, stmt.isConst)]]
            }
            else {
                let nstmt: TIRStatement[] = [];
                let nenv: StatementTypeEnvironment | undefined = undefined;

                const rhs = this.checkMultiExpressionAtAssign(env.createInitialEnvForExpressionEval(), stmt.exp, [undefined])[0];
                const rhstype = this.envExpressionGetInferType(rhs);
                this.raiseErrorIf(stmt.sinfo, rhstype.options.length !== 1 || !(rhstype.options[0] instanceof ResolvedEphemeralListType), `expression must be a multi return call but got ${rhstype.typeID}`);
                this.raiseErrorIf(stmt.sinfo, stmt.vars.some((vv) => vv.pos >= (rhstype.options[0] as ResolvedEphemeralListType).types.length), `too many variables for return value`);

                const ielist: ResolvedType[] = [];
                stmt.vars.forEach((vv) => {
                    if(vv.vtype instanceof AutoTypeSignature) {
                        ielist.push((rhstype.options[0] as ResolvedEphemeralListType).types[vv.pos]);
                    }
                    else {
                        ielist.push(this.normalizeTypeOnly(vv.vtype, env.binds));
                    }
                });

                const vvinfo = stmt.vars.map((vv, ii) => {
                    return {vname: vv.name, pos: vv.pos, vtype: this.toTIRTypeKey(ielist[ii])};
                });

                const packonly = stmt.vars.every((vv, ii) => vv.vtype instanceof AutoTypeSignature || (ielist[ii].typeID === (rhstype.options[0] as ResolvedEphemeralListType).types[vv.pos].typeID));
                const packtype = ResolvedType.createSingle(ResolvedEphemeralListType.create(ielist));
                const tirpacktype = this.toTIRTypeKey(packtype);

                const packonlymask = vvinfo.map((vv) => {
                    return vv.pos
                });

                const packconvmask = stmt.vars.map((vv, ii) => {
                    return {pos: vv.pos, totype: this.toTIRTypeKey(ielist[ii])};
                });

                stmt.vars.forEach((vv, ii) => {
                    this.raiseErrorIf(stmt.sinfo, !this.subtypeOf((rhstype.options[0] as ResolvedEphemeralListType).types[vv.pos], ielist[ii]), `cannot convert value safely -- expected ${ielist[ii].typeID} but got ${(rhstype.options[0] as ResolvedEphemeralListType).types[vv.pos].typeID}`);
                });

                if (rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
                    nenv = this.checkDeclareMultipleVariableExplicit(stmt.sinfo, env, stmt.isConst, vvdecls, this.envClearExps(rhs, rhs.expressionResult.thisref));

                    if(packonly) {
                        const conve = new TIRPackMultiExpression(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatementWRef(stmt.sinfo, vvinfo, conve, stmt.isConst, rhs.expressionResult.thisref)];
                    }
                    else {
                        const conve = new TIRCoerceRefCallMultiResultExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatementWRef(stmt.sinfo, vvinfo, conve, stmt.isConst, rhs.expressionResult.thisref)];
                    }
                }
                else if (rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefWithChecksExpression) {
                    nenv = this.checkDeclareMultipleVariableExplicit(stmt.sinfo, env, stmt.isConst, vvdecls, this.envClearExps(rhs, rhs.expressionResult.thisref));

                    if(packonly) {
                        const conve = new TIRPackMultiExpressionWRef(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatementWRef(stmt.sinfo, vvinfo, conve, stmt.isConst, rhs.expressionResult.thisref)];
                    }
                    else {
                        const conve = new TIRCoerceRefCallMultiResultExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatementWRef(stmt.sinfo, vvinfo, conve, stmt.isConst, rhs.expressionResult.thisref)];
                    }
                }
                else if (rhs.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
                    nenv = this.checkDeclareMultipleVariableExplicit(stmt.sinfo, env, stmt.isConst, vvdecls, this.envClearExps(rhs, "self"));

                    if(packonly) {
                        const conve = new TIRPackMultiExpressionWTaskRef(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatementWTaskRef(stmt.sinfo, vvinfo, conve, stmt.isConst, rhs.expressionResult.tsktype)];
                    }
                    else {
                        const conve = new TIRCoerceTaskRefCallMultiResultExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatementWTaskRef(stmt.sinfo, vvinfo, conve, stmt.isConst, rhs.expressionResult.tsktype)];
                    }
                }
                else if (rhs.expressionResult instanceof TIRCallMemberActionExpression) {
                    nenv = this.checkDeclareMultipleVariableExplicit(stmt.sinfo, env, stmt.isConst, vvdecls, this.envClearExps(rhs, "self"));

                    if(packonly) {
                        const conve = new TIRPackMultiExpressionWAction(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatementWAction(stmt.sinfo, vvinfo, conve, stmt.isConst, rhs.expressionResult.tsktype)];
                    }
                    else {
                        const conve = new TIRCoerceActionCallMultiResultExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatementWAction(stmt.sinfo, vvinfo, conve, stmt.isConst, rhs.expressionResult.tsktype)];
                    }
                }
                else {
                    nenv = this.checkDeclareMultipleVariableExplicit(stmt.sinfo, env, stmt.isConst, vvdecls, rhs);

                    if(packonly) {
                        const conve = new TIRPackMultiExpression(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatement(stmt.sinfo, vvinfo, conve, stmt.isConst)];
                    }
                    else {
                        const conve = new TIRCoerceSafeMultiExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                        nstmt = [new TIRMultiVarDeclareAndAssignStatement(stmt.sinfo, vvinfo, conve, stmt.isConst)];
                    }
                }

                return [nenv, nstmt];
            }
        }
    }

    private checkVariableAssignStatement(env: StatementTypeEnvironment, stmt: VariableAssignmentStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, env.getLocalVarInfo(stmt.name) === undefined, `variable ${stmt.name} not previously declared`);
        let rhs = this.checkExpressionAtAssign(env.createInitialEnvForExpressionEval(), stmt.exp, (env.getLocalVarInfo(stmt.name) as VarInfo).declaredType);

        let nstmt: TIRStatement[] = [];
        let nenv: StatementTypeEnvironment | undefined = undefined;
        if (rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, this.envClearExps(rhs, stmt.name, rhs.expressionResult.thisref));

            const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
            const refv = rhs.expressionResult.thisref;
            const rhsconv = this.emitRefCallCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

            nstmt = [new TIRVarAssignStatementWRef(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, refv)];
        }
        else if (rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefWithChecksExpression) {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, this.envClearExps(rhs, stmt.name, rhs.expressionResult.thisref));

            const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
            const refv = rhs.expressionResult.thisref;
            const rhsconv = this.emitRefCallCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

            nstmt = [new TIRVarAssignStatementWRef(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, refv)];
        }
        else if (rhs.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, this.envClearExps(rhs, stmt.name, "self"));

            const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
            const rhsconv = this.emitTaskRefCallCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

            nstmt = [new TIRVarAssignStatementWTaskRef(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, rhs.expressionResult.tsktype)];
        }
        else if (rhs.expressionResult instanceof TIRCallMemberActionExpression) {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, this.envClearExps(rhs, stmt.name, "self"));

            const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
            const rhsconv = this.emitActionCallCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

            nstmt = [new TIRVarAssignStatementWAction(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, rhs.expressionResult.tsktype)];
        }
        else {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, this.envClearExps(rhs, stmt.name));

            const dvtype = (nenv.lookupVar(stmt.name) as VarInfo).declaredType;
            const rhsconv = this.emitCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

            nstmt = [new TIRVarAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult)];
        }

        return [nenv, nstmt];
    }

    private checkMultiReturnVariableAssignmentStatement(env: StatementTypeEnvironment, stmt: MultiReturnWithAssignmentStatement): [StatementTypeEnvironment, TIRStatement[]] {
        for(let i = 0; i < stmt.vars.length; ++i) {
            this.raiseErrorIf(stmt.sinfo, env.getLocalVarInfo(stmt.vars[i].name) === undefined, `variable ${stmt.vars[i].name} not previously declared`);
        }
        
        const vvdecls = stmt.vars.map((vv) => vv.name);

        if (stmt.exp.length !== 1) {
            const itypes: (ResolvedType | undefined)[] = stmt.vars.map((vv) => {
                return (env.lookupVar(vv.name) as VarInfo).declaredType;
            });
            const rhsexps = this.checkMultiExpressionAtAssign(env.createInitialEnvForExpressionEval(), stmt.exp, itypes);

            this.raiseErrorIf(stmt.sinfo, stmt.exp.length !== rhsexps.length, `mismatch between number of variables assigned and number of expressions`);

            const ielist = ResolvedType.createSingle(ResolvedEphemeralListType.create(stmt.vars.map((vv) => (env.lookupVar(vv.name) as VarInfo).declaredType)));
            const createpack = new TIRConstructorEphemeralValueList(stmt.sinfo, this.toTIRTypeKey(ielist), rhsexps.map((rr, ii) => this.emitCoerceIfNeeded(rr, rr.expressionResult.sinfo, (ielist.options[0] as ResolvedEphemeralListType).types[ii]).expressionResult));

            const vvinfo = stmt.vars.map((vv, ii) => {
                return { vname: vv.name, pos: vv.pos, vtype: this.toTIRTypeKey((ielist.options[0] as ResolvedEphemeralListType).types[ii]) };
            });

            const declenv = this.checkAssignMultipleVariableExplicit(stmt.sinfo, env, vvdecls, this.setResultExpression(env.createInitialEnvForExpressionEval(), createpack, ielist, undefined));
            return [declenv, [new TIRMultiVarAssignStatement(stmt.sinfo, vvinfo, createpack)]]
        }
        else {
            let nstmt: TIRStatement[] = [];
            let nenv: StatementTypeEnvironment | undefined = undefined;

            const rhs = this.checkMultiExpressionAtAssign(env.createInitialEnvForExpressionEval(), stmt.exp, [undefined])[0];
            const rhstype = this.envExpressionGetInferType(rhs);
            this.raiseErrorIf(stmt.sinfo, rhstype.options.length !== 1 || !(rhstype.options[0] instanceof ResolvedEphemeralListType), `expression must be a multi return call but got ${rhstype.typeID}`);
            this.raiseErrorIf(stmt.sinfo, stmt.vars.some((vv) => vv.pos >= (rhstype.options[0] as ResolvedEphemeralListType).types.length), `too many variables for return value`);

            const ielist: ResolvedType[] = [];
            stmt.vars.forEach((vv) => {
                ielist.push((env.lookupVar(vv.name) as VarInfo).declaredType);
            });

            const vvinfo = stmt.vars.map((vv, ii) => {
                return { vname: vv.name, pos: vv.pos, vtype: this.toTIRTypeKey(ielist[ii]) };
            });

            const packonly = stmt.vars.every((vv, ii) => (ielist[ii].typeID === (rhstype.options[0] as ResolvedEphemeralListType).types[vv.pos].typeID));
            const packtype = ResolvedType.createSingle(ResolvedEphemeralListType.create(ielist));
            const tirpacktype = this.toTIRTypeKey(packtype);

            const packonlymask = vvinfo.map((vv) => {
                return vv.pos
            });

            const packconvmask = stmt.vars.map((vv, ii) => {
                return { pos: vv.pos, totype: this.toTIRTypeKey(ielist[ii]) };
            });

            stmt.vars.forEach((vv, ii) => {
                this.raiseErrorIf(stmt.sinfo, !this.subtypeOf((rhstype.options[0] as ResolvedEphemeralListType).types[vv.pos], ielist[ii]), `cannot convert value safely -- expected ${ielist[ii].typeID} but got ${(rhstype.options[0] as ResolvedEphemeralListType).types[vv.pos].typeID}`);
            });

            if (rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
                nenv = this.checkAssignMultipleVariableExplicit(stmt.sinfo, env, vvdecls, this.envClearExps(rhs, ...vvdecls, rhs.expressionResult.thisref));

                if (packonly) {
                    const conve = new TIRPackMultiExpression(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatementWRef(stmt.sinfo, vvinfo, conve, rhs.expressionResult.thisref)];
                }
                else {
                    const conve = new TIRCoerceRefCallMultiResultExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatementWRef(stmt.sinfo, vvinfo, conve, rhs.expressionResult.thisref)];
                }
            }
            else if (rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefWithChecksExpression) {
                nenv = this.checkAssignMultipleVariableExplicit(stmt.sinfo, env, vvdecls, this.envClearExps(rhs, ...vvdecls, rhs.expressionResult.thisref));

                if (packonly) {
                    const conve = new TIRPackMultiExpressionWRef(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatementWRef(stmt.sinfo, vvinfo, conve, rhs.expressionResult.thisref)];
                }
                else {
                    const conve = new TIRCoerceRefCallMultiResultExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatementWRef(stmt.sinfo, vvinfo, conve, rhs.expressionResult.thisref)];
                }
            }
            else if (rhs.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
                nenv = this.checkAssignMultipleVariableExplicit(stmt.sinfo, env, vvdecls, this.envClearExps(rhs, ...vvdecls, "self"));

                if (packonly) {
                    const conve = new TIRPackMultiExpressionWTaskRef(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatementWTaskRef(stmt.sinfo, vvinfo, conve, rhs.expressionResult.tsktype)];
                }
                else {
                    const conve = new TIRCoerceTaskRefCallMultiResultExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatementWTaskRef(stmt.sinfo, vvinfo, conve, rhs.expressionResult.tsktype)];
                }
            }
            else if (rhs.expressionResult instanceof TIRCallMemberActionExpression) {
                nenv = this.checkAssignMultipleVariableExplicit(stmt.sinfo, env, vvdecls, this.envClearExps(rhs, ...vvdecls, "self"));

                if (packonly) {
                    const conve = new TIRPackMultiExpressionWAction(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatementWAction(stmt.sinfo, vvinfo, conve, rhs.expressionResult.tsktype)];
                }
                else {
                    const conve = new TIRCoerceActionCallMultiResultExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatementWAction(stmt.sinfo, vvinfo, conve, rhs.expressionResult.tsktype)];
                }
            }
            else {
                nenv = this.checkAssignMultipleVariableExplicit(stmt.sinfo, env, vvdecls, this.envClearExps(rhs, ...vvdecls));

                if (packonly) {
                    const conve = new TIRPackMultiExpression(stmt.sinfo, rhs.expressionResult, packonlymask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatement(stmt.sinfo, vvinfo, conve)];
                }
                else {
                    const conve = new TIRCoerceSafeMultiExpression(stmt.sinfo, rhs.expressionResult, packconvmask, tirpacktype);
                    nstmt = [new TIRMultiVarAssignStatement(stmt.sinfo, vvinfo, conve)];
                }
            }

            return [nenv, nstmt];
        }
    }

    private checkReturnStatement(env: StatementTypeEnvironment, stmt: ReturnStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const rvals = stmt.values.map((vv, ii) => {
            return this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), vv, this.m_rtypes[ii]), vv.sinfo, this.m_rtypes[ii]);
        });

        return [env.endOfExecution(), [new TIRReturnStatement(stmt.sinfo, rvals.map((ee) => ee.expressionResult))]];
    }

    private checkAbortStatement(env: StatementTypeEnvironment, stmt: AbortStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return [env.endOfExecution(), [new TIRAbortStatement(stmt.sinfo, "Abort")]];
    }

    private checkAssertStatement(env: StatementTypeEnvironment, stmt: AssertStatement): [StatementTypeEnvironment, TIRStatement[]] {
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


    /*
    
    IfElseStatement = "IfElseStatement",
    SwitchStatement = "SwitchStatement",
    MatchStatement = "MatchStatement",

    AbortStatement = "AbortStatement",
    AssertStatement = "AssertStatement", //assert(x > 0)

    DebugStatement = "DebugStatement", //print an arg or if empty attach debugger
    RefCallStatement = "RefCallStatement",

    EnvironmentFreshStatement = "EnvironmentFreshStatement",
    EnvironmentSetStatement = "EnvironmentSetStatement",
    EnvironmentSetStatementBracket = "EnvironmentSetStatementBracket",

    TaskRunStatement = "TaskRunStatement", //run single task
    TaskMultiStatement = "TaskMultiStatement", //run multiple explicitly identified tasks -- complete all
    TaskDashStatement = "TaskDashStatement", //run multiple explicitly identified tasks -- first completion wins
    TaskAllStatement = "TaskAllStatement", //run the same task on all args in a list -- complete all
    TaskRaceStatement = "TaskRaceStatement", //run the same task on all args in a list -- first completion wins

    TaskCallWithStatement = "TaskCallWithStatement",
    TaskResultWithStatement = "TaskResultWithStatement",

    TaskSetStatusStatement = "TaskSetStatusStatement",

    TaskSetSelfFieldStatement = "TaskSetSelfFieldStatement",

    TaskEventEmitStatement = "TaskEventEmitStatement",

    LoggerEmitStatement = "LoggerEmitStatement",
    LoggerEmitConditionalStatement = "LoggerEmitConditionalStatement",

    LoggerLevelStatement = "LoggerLevelStatement",
    LoggerCategoryStatement = "LoggerCategoryStatement",
    LoggerPrefixStatement = "LoggerPrefixStatement",

    UnscopedBlockStatement = "UnscopedBlockStatement",
    ScopedBlockStatement = "ScopedBlockStatement"
*/

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
