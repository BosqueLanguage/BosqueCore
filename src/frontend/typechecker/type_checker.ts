//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { Assembly, ConceptTypeDecl, EntityTypeDecl, InfoTemplate, InfoTemplateConst, InfoTemplateMacro, InfoTemplateRecord, InfoTemplateTuple, InfoTemplateValue, InvokeDecl, MemberFieldDecl, MemberMethodDecl, NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, NamespaceTypedef, OOMemberDecl, OOPTypeDecl, PathValidator, PostConditionDecl, PreConditionDecl, StaticFunctionDecl, StaticMemberDecl, TaskTypeDecl, TemplateTermDecl, TypeConditionRestriction } from "../ast/assembly";
import { ResolvedASCIIStringOfEntityAtomType, ResolvedAtomType, ResolvedConceptAtomType, ResolvedConceptAtomTypeEntry, ResolvedOkEntityAtomType, ResolvedErrEntityAtomType, ResolvedSomethingEntityAtomType, ResolvedMapEntryEntityAtomType, ResolvedEntityAtomType, ResolvedEnumEntityAtomType, ResolvedFunctionType, ResolvedHavocEntityAtomType, ResolvedListEntityAtomType, ResolvedMapEntityAtomType, ResolvedObjectEntityAtomType, ResolvedPathEntityAtomType, ResolvedPathFragmentEntityAtomType, ResolvedPathGlobEntityAtomType, ResolvedPathValidatorEntityAtomType, ResolvedPrimitiveInternalEntityAtomType, ResolvedQueueEntityAtomType, ResolvedRecordAtomType, ResolvedSetEntityAtomType, ResolvedStackEntityAtomType, ResolvedStringOfEntityAtomType, ResolvedTaskAtomType, ResolvedTupleAtomType, ResolvedType, ResolvedTypedeclEntityAtomType, ResolvedValidatorEntityAtomType, TemplateBindScope, ResolvedFunctionTypeParam, ResolvedConstructableEntityAtomType, ResolvedPrimitiveCollectionEntityAtomType } from "./resolved_type";
import { AccessEnvValueExpression, AccessFormatInfoExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndxpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionExpression, ConstantExpressionValue, ConstructorPCodeExpression, ConstructorPrimaryExpression, ConstructorRecordExpression, ConstructorTupleExpression, Expression, ExpressionTag, IfExpression, LiteralASCIIStringExpression, LiteralASCIITemplateStringExpression, LiteralASCIITypedStringExpression, LiteralBoolExpression, LiteralExpressionValue, LiteralFloatPointExpression, LiteralIntegralExpression, LiteralNoneExpression, LiteralNothingExpression, LiteralRationalExpression, LiteralRegexExpression, LiteralStringExpression, LiteralTemplateStringExpression, LiteralTypedPrimitiveConstructorExpression, LiteralTypedStringExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchExpression, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, PCodeInvokeExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixInvoke, PostfixIsTest, PostfixOp, PostfixOpTag, PrefixNegateOp, PrefixNotOp, SpecialConstructorExpression, SwitchExpression, TaskSelfFieldExpression, TaskSelfActionExpression, TaskGetIDExpression, Statement, EmptyStatement, VariableDeclarationStatement, VariableAssignmentStatement, ReturnStatement, AbortStatement, AssertStatement, DebugStatement, IfStatement, UnscopedBlockStatement, SwitchStatement, MatchStatement, RefCallStatement, EnvironmentFreshStatement, EnvironmentSetStatement, EnvironmentSetStatementBracket, TaskRunStatement, TaskMultiStatement, TaskDashStatement, TaskAllStatement, TaskRaceStatement, TaskSelfControlExpression, TaskCallWithStatement, TaskResultWithStatement, TaskSetStatusStatement, TaskSetSelfFieldStatement, TaskEventEmitStatement, LoggerEmitStatement, LoggerEmitConditionalStatement, LoggerLevelStatement, LoggerCategoryStatement, LoggerPrefixStatement, StatementTag, ScopedBlockStatement, BodyImplementation, VariableRetypeStatement, ITest, ITestType, ITestLiteral, ITestErr, ITestNone, ITestNothing, ITestSomething, ITestOk, ExpressionSCReturnStatement, VariableSCRetypeStatement, ITestSome } from "../ast/body";
import { AndTypeSignature, AutoTypeSignature, FunctionParameter, FunctionTypeSignature, NominalTypeSignature, ParseErrorTypeSignature, ProjectTypeSignature, RecordTypeSignature, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature } from "../ast/type";
import { ExpressionTypeEnvironment, VarInfo, StatementTypeEnvironment } from "./type_environment";

import { TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessConstMemberFieldExpression, TIRAccessVariableExpression, TIRExpression, TIRInvalidExpression, TIRLiteralASCIIStringExpression, TIRLiteralASCIITemplateStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression, TIRLiteralStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralTypedPrimitiveConstructorExpression, TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedStringExpression, TIRLiteralValue, TIRCoerceSafeExpression, TIRConstructorPrimaryDirectExpression, TIRResultOkConstructorExpression, TIRResultErrConstructorExpression, TIRSomethingConstructorExpression, TIRMapEntryConstructorExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorListExpression, TIRConstructorMapExpression, TIRConstructorTupleExpression, TIRConstructorRecordExpression, TIRCodePack, TIRTypedeclDirectExpression, TIRTypedeclConstructorExpression, TIRCallNamespaceFunctionExpression, TIRCallNamespaceOperatorExpression, TIRBinKeyEqBothUniqueExpression, TIRBinKeyEqOneUniqueExpression, TIRBinKeyEqGeneralExpression, TIRBinKeyUniqueLessExpression, TIRBinKeyGeneralLessExpression, TIRInjectExpression, TIRCallStaticFunctionExpression, TIRLogicActionAndExpression, TIRIsTypeExpression, TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression, TIRExtractExpression, TIRCallMemberFunctionSelfRefExpression, TIRCallMemberFunctionExpression, TIRCallMemberFunctionDynamicExpression, TIRPrefixNotExpression, TIRStatement, TIRPrefixNegateExpression, TIRBinKeyNeqBothUniqueExpression, TIRBinKeyNeqOneUniqueExpression, TIRBinKeyNeqGeneralExpression, TIRLogicActionOrExpression, TIRBinLogicOrExpression, TIRBinAddExpression, TIRBinSubExpression, TIRBinMultExpression, TIRBinDivExpression, TIRNumericEqExpression, TIRNumericNeqExpression, TIRNumericLessExpression, TIRNumericLessEqExpression, TIRNumericGreaterExpression, TIRNumericGreaterEqExpression, TIRIfExpression, TIRSwitchExpression, TIRMatchExpression, TIRTaskSelfFieldExpression, TIRTaskGetIDExpression, TIRCallMemberActionExpression, TIRVarDeclareStatement, TIRCallMemberFunctionTaskSelfRefExpression, TIRCallMemberFunctionTaskExpression, TIRVarDeclareAndAssignStatement, TIRVarAssignStatement, TIRReturnStatement, TIRReturnStatementWRef, TIRReturnStatementWTaskRef, TIRReturnStatementWAction, TIRAbortStatement, TIRAssertCheckStatement, TIRDebugStatement, TIRBinLogicAndExpression, TIRScopedBlockStatement, TIRUnscopedBlockStatement, TIRIfStatement, TIRNopStatement, TIRSwitchStatement, TIRMatchStatement, TIREnvironmentFreshStatement, TIREnvironmentSetStatement, TIREnvironmentSetStatementBracket, TIRTaskSelfControlExpression, TIRTaskRunStatement, TIRTaskMultiStatement, TIRTaskDashStatement, TIRTaskAllStatement, TIRTaskRaceStatement, TIRTaskSetSelfFieldStatement, TIRLoggerEmitStatement, TIRLoggerEmitConditionalStatement, TIRCreateCodePackExpression, TIRAccessCapturedVariableExpression, TIRCodePackInvokeExpression, TIRLoggerSetPrefixStatement, TIRBinLogicImpliesExpression, TIRIsNoneSpecialExpression, TIRIsSomeSpecialExpression, TIRIsNothingSpecialExpression, TIRIsSomethingSpecialExpression, TIRIsErrSpecialExpression, TIRIsOkSpecialExpression, TIRIsNotEqualToLiteralExpression, TIRIsEqualToLiteralExpression, TIRIsNotSubTypeExpression, TIRIsNotTypeExpression, TIRIsSubTypeExpression, TIRAsSomeSpecialExpression, TIRAsNoneSpecialExpression, TIRAsSomethingSpecialExpression, TIRAsNothingSpecialExpression, TIRAsErrSpecialExpression, TIRAsOkSpecialExpression, TIRAsEqualToLiteralExpression, TIRAsNotEqualToLiteralExpression, TIRAsNotTypeExpression, TIRAsNotSubTypeExpression, TIRAsTypeExpression, TIRAsSubTypeExpression, TIRAccessScratchSingleValueExpression, TIRAccessScratchIndexExpression, TIRCallStatementWRef, TIRVarRefAssignFromScratch, TIRTaskRefAssignFromScratch, TIRCallStatementWTaskRef, TIRCallStatementWAction, TIRVariableRetypeStatement, TIRVariableSCRetypeStatement } from "../tree_ir/tir_body";
import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptSetType, TIRConceptType, TIRConstMemberDecl, TIREnumEntityType, TIRErrEntityType, TIRFieldKey, TIRFunctionParameter, TIRHavocEntityType, TIRInfoTemplate, TIRInfoTemplateConst, TIRInfoTemplateMacro, TIRInfoTemplateRecord, TIRInfoTemplateTuple, TIRInfoTemplateValue, TIRInvoke, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokeKey, TIRInvokePrimitive, TIRListEntityType, TIRMapEntityType, TIRMapEntryEntityType, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIRNamespaceLambdaDecl, TIRNamespaceOperatorDecl, TIRObjectEntityType, TIRObjectInvariantDecl, TIRObjectValidateDecl, TIROkEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPCodeKey, TIRPostConditionDecl, TIRPreConditionDecl, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRSomethingEntityType, TIRStackEntityType, TIRStaticFunctionDecl, TIRStringOfEntityType, TIRStringTemplate, TIRTaskType, TIRTupleType, TIRType, TIRTypedeclEntityType, TIRTypedeclInvariantDecl, TIRTypedeclValidateDecl, TIRTypeKey, TIRTypeName, TIRUnionType, TIRValidatorEntityType } from "../tree_ir/tir_assembly";

import { BSQRegex, RegexAlternation, RegexCharRange, RegexComponent, RegexConstClass, RegexDotCharClass, RegexLiteral, RegexOptional, RegexPlusRepeat, RegexRangeRepeat, RegexSequence, RegexStarRepeat } from "../bsqregex";
import { extractLiteralStringValue, extractLiteralASCIIStringValue, SourceInfo, BuildLevel, isBuildLevelEnabled, PackageConfig } from "../build_decls";
import { Parser } from "../ast/parser";

import * as path from "path";

function assert(cond: boolean, msg?: string) {
    if(!cond) {
        throw new Error((msg || "error")  + " -- type_checker.ts");
    }
} 

function TYPECHECKER_TODO<T>(action: string): T {
    console.log(`TODO: ${action}`);
    assert(false);

    return (undefined as any) as T;
}

function TYPECHECKER_NOT_IMPLEMENTED<T>(f: string): T {
    return TYPECHECKER_TODO<T>(f);
}

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

class TIRIDGenerator {
    static generateTermsBinds(terms: TIRTypeKey[]): string {
        if(terms.length === 0) {
            return "";
        }

        return `<${terms.join(", ")}>`;
    }

    static generatePCodeBinds(pcodes: TIRPCodeKey[]): string {
        if(pcodes.length === 0) {
            return "";
        }

        return `[${pcodes.join(", ")}]`;
    }

    static generatePCodeIDInfoForLambda(srcfile: string, sinfo: SourceInfo, lambdaid: number, terms: TIRTypeKey[], pcodes: TIRPCodeKey[]): [TIRPCodeKey, TIRInvokeKey] {
        const pcc = `$Lambda_$${lambdaid}$${sinfo.line}`;
        const invk = pcc + "_invk";

        return [pcc, invk];
    }

    static generateInvokeIDForNamespaceFunction(ns: string, name: string, terms: TIRTypeKey[], pcodes: TIRPCodeKey[]): TIRInvokeKey {
        return `${ns}::${name}${TIRIDGenerator.generateTermsBinds(terms)}${TIRIDGenerator.generatePCodeBinds(pcodes)}`;
    }

    static generateInvokeIDForNamespaceOperatorBase(ns: string, name: string): TIRInvokeKey {
        return `operator_base_${ns}::${name}`;
    }

    static generateInvokeIDForNamespaceOperatorImpl(ns: string, name: string, idx: number): TIRInvokeKey {
        return `operator_impl_${idx}_${ns}::${name}`;
    }

    static generateInvokeForMemberFunction(ttype: TIRTypeKey, name: string, terms: TIRTypeKey[], pcodes: TIRPCodeKey[]): TIRInvokeKey {
        return `${ttype}::${name}${TIRIDGenerator.generateTermsBinds(terms)}${TIRIDGenerator.generatePCodeBinds(pcodes)}`;
    }

    static generateInvokeForMemberMethod(ttype: TIRTypeKey, name: string, terms: TIRTypeKey[], pcodes: TIRPCodeKey[]): TIRInvokeKey {
        return `${ttype}::${name}${TIRIDGenerator.generateTermsBinds(terms)}${TIRIDGenerator.generatePCodeBinds(pcodes)}`;
    }

    static generateMemberFieldID(typeid: string, fname: string): TIRFieldKey {
        return `${typeid}$${fname}`;
    }
}

enum ReturnMode {
    Standard,
    MemberRef,
    MemberSelf,
    MemberAction
}

class TypeChecker {
    private readonly m_assembly: Assembly;
    private m_buildLevel: BuildLevel;
    private m_issmtbuild: boolean;
    private m_istestbuild: boolean;

    private m_file: string;
    private m_ns: string;
    private m_rtype: ResolvedType;
    private m_returnMode: ReturnMode;
    private m_taskOpsOk: boolean;
    private m_taskSelfOk: "no" | "read" | "write";
    private m_taskType: {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>} | undefined;
    private m_errors: [string, number, string][];

    private m_specialTypeMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private m_typedefResolutions: Map<string, ResolvedType> = new Map<string, ResolvedType>();

    private m_tirTypeMap: Map<string, TIRType> = new Map<string, TIRType>();
    private m_tirNamespaceMap: Map<string, TIRNamespaceDeclaration> = new Map<string, TIRNamespaceDeclaration>();
    private m_tirFieldMap: Map<string, TIRMemberFieldDecl> = new Map<string, TIRMemberFieldDecl>();
    private m_tirInvokeMap: Map<string, TIRInvoke> = new Map<string, TIRInvoke>();
    private m_tirCodePackMap: Map<TIRPCodeKey, TIRCodePack> = new Map<TIRPCodeKey, TIRCodePack>();
    private m_toTIRprocessingstack: ResolvedAtomType[] = [];

    private m_instantiatedVTableTypes: ResolvedObjectEntityAtomType[] = [];

    private m_pendingEntityDecls: {tirtype: TIRObjectEntityType, rtype: ResolvedEntityAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>}[] = [];
    private m_pendingEnumDecls: {tirtype: TIREnumEntityType, rtype: ResolvedEnumEntityAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>}[] = [];
    private m_pendingTypedeclDecls: {tirtype: TIRTypedeclEntityType, rtype: ResolvedTypedeclEntityAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>}[] = [];
    private m_pendingConceptDecls: {tirtype: TIRConceptType, rtype: ResolvedConceptAtomTypeEntry, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>}[] = [];
    private m_pendingTaskDecls: {tirtype: TIRTaskType, rtype: ResolvedTaskAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>}[] = [];

    private m_pendingNamespaceConsts: NamespaceConstDecl[] = [];
    private m_pendingNamespaceFunctions: {fkey: TIRInvokeKey, decl: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>}[] = [];
    private m_pendingNamespaceOperators: {fkey: TIRInvokeKey, decl: NamespaceOperatorDecl, impls: {fkey: TIRInvokeKey, decl: NamespaceOperatorDecl}[]}[] = [];

    private m_pendingConstMemberDecls: OOMemberLookupInfo<StaticMemberDecl>[] = [];
    private m_pendingFunctionMemberDecls: {fkey: TIRInvokeKey, decl: OOMemberLookupInfo<StaticFunctionDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>}[] = [];
    private m_pendingMethodMemberDecls: {fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, declaredecl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>}[] = [];

    private m_lambdaCtr = 0;
    private m_pendingCodeDecls: {cpdata: TIRCodePack, cpdecl: InvokeDecl, desiredfunc: ResolvedFunctionType, declbinds: TemplateBindScope, bodybinds: Map<string, ResolvedType>, capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, capturedvars: Map<string, {vname: string, vtype: ResolvedType}>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>}[] = [];

    private m_scratchCtr = 0;

    constructor(assembly: Assembly, buildlevel: BuildLevel, overflowisfailure: boolean, issmtbuild: boolean, istestbuild: boolean) {
        this.m_assembly = assembly;

        this.m_buildLevel = buildlevel;
        this.m_issmtbuild = issmtbuild;
        this.m_istestbuild = istestbuild;

        this.m_file = "[No File]";
        this.m_ns = "[NOT SET]";
        this.m_rtype = this.getSpecialNoneType();
        this.m_returnMode = ReturnMode.Standard;
        this.m_taskOpsOk = false;
        this.m_taskSelfOk = "no";
        this.m_scratchCtr = 0;
        this.m_errors = [];
        
        TIRExpression.OverflowIsFailure = overflowisfailure;
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

    reduceLiteralValueToCanonicalForm(exp: Expression, binds: TemplateBindScope): [TIRLiteralValue | undefined, ResolvedType] {
        const cexp = this.compileTimeReduceConstantExpression(exp, binds);
        if(cexp === undefined) {
            return [undefined, ResolvedType.createInvalid()];
        }

        const literalenv = ExpressionTypeEnvironment.createInitialEnvForLiteralEval(binds);
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
                return [undefined, ResolvedType.createInvalid()];
            }
        }

        const tlit = new TIRLiteralValue(nexp.expressionResult, nexp.expressionResult.expstr); 

        return [tlit, nexp.trepr];
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

    private processBSQRegex(sinfo: SourceInfo, re: BSQRegex): BSQRegex {
        return new BSQRegex(re.regexstr, this.processRegexComponent(sinfo, re.re));
    }

    private processValidatorRegex(sinfo: SourceInfo, vtype: string): BSQRegex {
        const reopt = this.m_assembly.tryGetValidatorForFullyResolvedName(vtype);
        this.raiseErrorIf(sinfo, reopt === undefined, `missing regex for validator ${vtype}`);

        return this.processBSQRegex(sinfo, reopt as BSQRegex);
    }

    private splitConceptTypes(ofc: ResolvedConceptAtomType, withc: ResolvedConceptAtomType): {tp: ResolvedType | undefined, fp: ResolvedType | undefined} {
        if (ofc.typeID === "Any" && withc.typeID === "Some") {
            return { tp: ResolvedType.createSingle(withc), fp: this.getSpecialNoneType() };
        }
        else if (ofc.typeID.startsWith("Option<") && withc.typeID === "ISomething") {
            const somthingres = ResolvedSomethingEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("Something") as EntityTypeDecl, ofc.conceptTypes[0].binds.get("T") as ResolvedType)
            return { tp: ResolvedType.createSingle(somthingres), fp: this.getSpecialNothingType() };
        }
        else if (ofc.typeID === "IOption" && withc.typeID === "ISomething") {
            return { tp: ResolvedType.createSingle(withc), fp: this.getSpecialNothingType() };
        }
        else {
            const nand = this.normalizeAndList([...withc.conceptTypes, ...ofc.conceptTypes]);
            return { tp: nand, fp: ResolvedType.createSingle(ofc) };
        }
    }

    private splitConceptEntityTypes(ofc: ResolvedConceptAtomType, withe: ResolvedEntityAtomType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        const somethingdecl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("Something") as EntityTypeDecl;
        const okdecl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("Result::Ok") as EntityTypeDecl;
        const errdecl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("Result::Err") as EntityTypeDecl;

        //
        //TODO: we may want to handle some ISomething, Something, Option, Nothing situations more precisely if they can arise
        //

        if (ofc.typeID === "Any" && withe.typeID === "None") {
            return { tp: ResolvedType.createSingle(withe), fp: this.getSpecialSomeConceptType() };
        }
        else if (ofc.typeID.startsWith("Option<") && withe.typeID === "Nothing") {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedSomethingEntityAtomType.create(somethingdecl, ofc.conceptTypes[0].binds.get("T") as ResolvedType)) };
        }
        else if (ofc.typeID.startsWith("Option<") && withe.typeID === "Something<") {
            return { tp: ResolvedType.createSingle(withe), fp: this.getSpecialNothingType() };
        }
        else if (ofc.typeID.startsWith("Result<") && withe.typeID.startsWith("Result::Ok<")) {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedOkEntityAtomType.create(errdecl, ofc.conceptTypes[0].binds.get("T") as ResolvedType, ofc.conceptTypes[0].binds.get("E") as ResolvedType)) };
        }
        else if (ofc.typeID.startsWith("Result<") && withe.typeID.startsWith("Result::Err<")) {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ResolvedErrEntityAtomType.create(okdecl, ofc.conceptTypes[0].binds.get("T") as ResolvedType, ofc.conceptTypes[0].binds.get("E") as ResolvedType)) };
        }
        else if(this.atomSubtypeOf(withe, ofc)) {
            return { tp: ResolvedType.createSingle(withe), fp: ResolvedType.createSingle(ofc) };
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

    private splitTypes(oft: ResolvedType, witht: ResolvedType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        if (oft.isInvalidType() || witht.isInvalidType()) {
            return { tp: undefined, fp: undefined };
        }

        if (oft.typeID === witht.typeID) {
            return { tp: oft, fp: undefined };
        }

        const paths = oft.options.map((opt) => this.splitAtomWithType(opt, witht));
        let tp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.tp));
        let fp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.fp));

        return {tp: this.normalizeUnionList(tp), fp: this.normalizeUnionList(fp)};
    }

    private processITestAsTest_None(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        const tsplit = this.splitTypes(flowtype, this.getSpecialNoneType());

        if(isnot) {
            return { testexp: new TIRIsSomeSpecialExpression(sinfo, tirexp), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
        }
        else {
            return { testexp: new TIRIsNoneSpecialExpression(sinfo, tirexp), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
        }
    }

    private processITestAsTest_Some(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        const tsplit = this.splitTypes(flowtype, this.getSpecialSomeConceptType());

        if(isnot) {
            return { testexp: new TIRIsNoneSpecialExpression(sinfo, tirexp), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
        }
        else {
            return { testexp: new TIRIsSomeSpecialExpression(sinfo, tirexp), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
        }
    }

    private processITestAsTest_Nothing(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        this.raiseErrorIf(sinfo, !flowtype.isOptionType() && !flowtype.isNothingType() && !flowtype.isSomethingType(), "Special nothing test is only valid on Option<T> types (not part of a union etc.)");
        const tsplit = this.splitTypes(flowtype, this.getSpecialNothingType());

        if(isnot) {
            return { testexp: new TIRIsSomethingSpecialExpression(sinfo, tirexp), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
        }
        else {
            return { testexp: new TIRIsNothingSpecialExpression(sinfo, tirexp), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
        }
    }

    private processITestAsTest_Something(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        this.raiseErrorIf(sinfo, !flowtype.isOptionType() && !flowtype.isNothingType() && !flowtype.isSomethingType(), "Special something test is only valid on Option<T> types (not part of a union etc.)");
        const tsplit = this.splitTypes(flowtype, this.getSpecialNothingType());

        if(isnot) {
            return { testexp: new TIRIsNothingSpecialExpression(sinfo, tirexp), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
        }
        else {
            return { testexp: new TIRIsSomethingSpecialExpression(sinfo, tirexp), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
        }
    }

    private processITestAsTest_Ok(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        this.raiseErrorIf(sinfo, !flowtype.isResultType() && !flowtype.isOkType() && !flowtype.isErrType(), "Special ok test is only valid on Result<T, E> types (not part of a union etc.)");
        const binds = flowtype.isResultType() ? (flowtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds : (flowtype.options[0] as ResolvedConstructableEntityAtomType).getBinds();
        const oktype = this.getOkType(binds.get("T") as ResolvedType, binds.get("E") as ResolvedType);
        const errtype = this.getErrType(binds.get("T") as ResolvedType, binds.get("E") as ResolvedType);
        const tsplit = this.splitTypes(flowtype, oktype);

        if(isnot) {
            return { testexp: new TIRIsErrSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(errtype)), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
        }
        else {
            return { testexp: new TIRIsOkSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(oktype)), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
        }
    }

    private processITestAsTest_Err(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        this.raiseErrorIf(sinfo, !flowtype.isResultType() && !flowtype.isOkType() && !flowtype.isErrType(), "Special ok test is only valid on Result<T, E> types (not part of a union etc.)");
        const binds = flowtype.isResultType() ? (flowtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds : (flowtype.options[0] as ResolvedConstructableEntityAtomType).getBinds();
        const oktype = this.getOkType(binds.get("T") as ResolvedType, binds.get("E") as ResolvedType);
        const errtype = this.getErrType(binds.get("T") as ResolvedType, binds.get("E") as ResolvedType);
        const tsplit = this.splitTypes(flowtype, errtype);

        if(isnot) {
            return { testexp: new TIRIsOkSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(oktype)), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
        }
        else {
            return { testexp: new TIRIsErrSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(errtype)), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
        }
    }

    private processITestAsTest_Literal(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, literal: LiteralExpressionValue, literaltype: ResolvedType, tirexp: TIRExpression, tirliteral: TIRLiteralValue, isnot: boolean): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        if(isnot) {
            let tptype: ResolvedType | undefined = undefined;
            let fptype: ResolvedType | undefined = undefined;

            if(literal.exp instanceof LiteralNoneExpression || literal.exp instanceof LiteralNothingExpression) {
                const tsplit = this.splitTypes(flowtype, literaltype);

                tptype = tsplit.fp;
                fptype = literaltype;
            }
            else {
                tptype = flowtype;
                fptype = flowtype;
            }

            return { testexp: new TIRIsNotEqualToLiteralExpression(sinfo, tirexp, tirliteral), falseflow: fptype, hastrueflow: tptype !== undefined  };
        }
        else {
            let tptype: ResolvedType | undefined = undefined;
            let fptype: ResolvedType | undefined = undefined;

            if(literal.exp instanceof LiteralNoneExpression || literal.exp instanceof LiteralNothingExpression) {
                const tsplit = this.splitTypes(flowtype, literaltype);

                tptype = literaltype;
                fptype = tsplit.fp;
            }
            else {
                tptype = flowtype;
                fptype = flowtype;
            }

            return { testexp: new TIRIsEqualToLiteralExpression(sinfo, tirexp, tirliteral), falseflow: fptype, hastrueflow: tptype !== undefined };
        }
    }

    private processITestAsTest_Type(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, intotype: ResolvedType, isnot: boolean): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        const tsplit = this.splitTypes(flowtype, intotype);

        if(isnot) {
            if(intotype.options.length === 1 && ResolvedType.isUniqueType(intotype.options[0])) {
                if(intotype.isNoneType()) {
                    return { testexp: new TIRIsSomeSpecialExpression(sinfo, tirexp), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
                }
                else if(intotype.isNothingType()) {
                    return { testexp: new TIRIsSomethingSpecialExpression(sinfo, tirexp), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
                }
                else {
                    return { testexp: new TIRIsNotTypeExpression(sinfo, tirexp, this.toTIRTypeKey(intotype)), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
                }
            }
            else {
                if(intotype.isSomeType()) {
                    return { testexp: new TIRIsNoneSpecialExpression(sinfo, tirexp), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
                }
                else {
                    return { testexp: new TIRIsNotSubTypeExpression(sinfo, tirexp, this.toTIRTypeKey(intotype)), falseflow: tsplit.tp, hastrueflow: tsplit.fp !== undefined };
                }
            }
        }
        else {
            if(intotype.options.length === 1 && ResolvedType.isUniqueType(intotype.options[0])) {
                if(intotype.isNoneType()) {
                    return { testexp: new TIRIsNoneSpecialExpression(sinfo, tirexp), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
                }
                else if(intotype.isNothingType()) {
                    return { testexp: new TIRIsNothingSpecialExpression(sinfo, tirexp), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
                }
                else {
                    return { testexp: new TIRIsTypeExpression(sinfo, tirexp, this.toTIRTypeKey(intotype)), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
                }
            }
            else {
                if(intotype.isSomeType()) {
                    return { testexp: new TIRIsSomeSpecialExpression(sinfo, tirexp), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
                }
                else {
                    return { testexp: new TIRIsSubTypeExpression(sinfo, tirexp, this.toTIRTypeKey(intotype)), falseflow: tsplit.fp, hastrueflow: tsplit.tp !== undefined };
                }
            }
        }
    }
    
    private processITestAsTestOp(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, tt: ITest, binds: TemplateBindScope): {testexp: TIRExpression, falseflow: ResolvedType | undefined, hastrueflow: boolean} {
        if(tt instanceof ITestType) {
            const intotype = this.normalizeTypeOnly(tt.ttype, binds);
            return this.processITestAsTest_Type(sinfo, ltype, flowtype, tirexp, intotype, tt.isnot);
        }
        else if(tt instanceof ITestLiteral) {
            const [tirliteral, ltype] = this.reduceLiteralValueToCanonicalForm(tt.literal.exp, binds);
            this.raiseErrorIf(sinfo, tirliteral === undefined, `could not evaluate literal value`);

            return this.processITestAsTest_Literal(sinfo, ltype, flowtype, tt.literal, ltype, tirexp, tirliteral as TIRLiteralValue, tt.isnot);
        }
        else {
            if(tt instanceof ITestNone) {
                return this.processITestAsTest_None(sinfo, ltype, flowtype, tirexp, tt.isnot);
            }
            else if(tt instanceof ITestSome) {
                return this.processITestAsTest_Some(sinfo, ltype, flowtype, tirexp, tt.isnot);
            }
            else if(tt instanceof ITestNothing) {
                return this.processITestAsTest_Nothing(sinfo, ltype, flowtype, tirexp, tt.isnot);
            }
            else if(tt instanceof ITestSomething) {
                return this.processITestAsTest_Something(sinfo, ltype, flowtype, tirexp, tt.isnot);
            }
            else if(tt instanceof ITestOk) {
                return this.processITestAsTest_Ok(sinfo, ltype, flowtype, tirexp, tt.isnot);
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                return this.processITestAsTest_Err(sinfo, ltype, flowtype, tirexp, tt.isnot);
            }
        }
    }

    private processITestAsConvert_None(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        const tsplit = this.splitTypes(flowtype, this.getSpecialNoneType());
        issafe = issafe || (isnot ? tsplit.tp === undefined : tsplit.fp === undefined);

        if (issafe) {
            if (isnot) {
                return { 
                    asexp: tsplit.fp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.fp) : undefined, 
                    asnotexp: tsplit.tp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.tp) : undefined, 
                    trueflow: tsplit.fp, 
                    falseflow: tsplit.tp 
                };
            }
            else {
                return { 
                    asexp: tsplit.tp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.tp) : undefined, 
                    asnotexp: tsplit.fp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.fp) : undefined, 
                    trueflow: tsplit.tp, 
                    falseflow: tsplit.fp 
                };
            }
        }
        else {
            if (isnot) {
                return { 
                    asexp: tsplit.fp !== undefined ? new TIRAsSomeSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp)) : undefined, 
                    asnotexp: new TIRAsNoneSpecialExpression(sinfo, tirexp), 
                    trueflow: tsplit.fp, 
                    falseflow: tsplit.tp 
                };
            }
            else {
                return { 
                    asexp: new TIRAsNoneSpecialExpression(sinfo, tirexp), 
                    asnotexp: tsplit.tp !== undefined ? new TIRAsSomeSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.tp)) : undefined, 
                    trueflow: tsplit.tp, 
                    falseflow: tsplit.fp 
                };
            }
        }
    }

    private processITestAsConvert_Some(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        const tsplit = this.splitTypes(flowtype, this.getSpecialSomeConceptType());
        issafe = issafe || (isnot ? tsplit.tp === undefined : tsplit.fp === undefined);

        if (issafe) {
            if (isnot) {
                return { 
                    asexp: tsplit.fp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.fp) : undefined, 
                    asnotexp: tsplit.tp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.tp) : undefined, 
                    trueflow: tsplit.fp, 
                    falseflow: tsplit.tp 
                };
            }
            else {
                return { 
                    asexp: tsplit.tp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.tp) : undefined, 
                    asnotexp: tsplit.fp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.fp) : undefined, 
                    trueflow: tsplit.tp, 
                    falseflow: tsplit.fp 
                };
            }
        }
        else {
            if (isnot) {
                return { 
                    asexp: new TIRAsNoneSpecialExpression(sinfo, tirexp), 
                    asnotexp: tsplit.tp !== undefined ? new TIRAsSomeSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.tp)) : undefined, 
                    trueflow: tsplit.fp, 
                    falseflow: tsplit.tp 
                };
            }
            else {
                return { 
                    asexp: tsplit.fp !== undefined ? new TIRAsSomeSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp)) : undefined, 
                    asnotexp: new TIRAsNoneSpecialExpression(sinfo, tirexp), 
                    trueflow: tsplit.tp, 
                    falseflow: tsplit.fp 
                };
            }
        }
    }

    private processITestAsConvert_Nothing(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        this.raiseErrorIf(sinfo, !flowtype.isOptionType() && !flowtype.isSomethingType() && !flowtype.isNothingType(), "Special nothing test is only valid on Option<T> types (not part of a union etc.)");
        if (flowtype.isNothingType()) {
            if (isnot) {
                //(nothing)@!nothing -- x, nothing, x, Nothing
                return {
                    asexp: undefined,
                    asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, this.getSpecialNothingType()),
                    trueflow: undefined,
                    falseflow: this.getSpecialNothingType()
                };
            }
            else {
                //(nothing)@nothing -- nothing, x, Nothing, x
                return {
                    asexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, this.getSpecialNothingType()),
                    asnotexp: undefined,
                    trueflow: this.getSpecialNothingType(),
                    falseflow: undefined
                };
            }
        }
        else if(flowtype.isSomethingType()) {
            const typet = (flowtype.options[0] as ResolvedSomethingEntityAtomType).typeT;
            if (isnot) {
                //(something(t))@!nothing -- t, x, T, x
                return {
                    asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, flowtype), this.toTIRTypeKey(typet)),
                    asnotexp: undefined,
                    trueflow: typet,
                    falseflow: undefined
                };
            }
            else {
                //(something(t))@nothing -- x, something(t), x, Something<T>
                return {
                    asexp: undefined,
                    asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, flowtype),
                    trueflow: undefined,
                    falseflow: flowtype
                };
            }
        }
        else {
            const binds = (flowtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
            const typet = binds.get("T") as ResolvedType;
            const somethingtype = this.getSomethingType(typet);

            if (issafe) {
                if (isnot) {
                    //(option t)@!nothing -- t, nothing, T, Nothing
                    return { 
                        asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, somethingtype), this.toTIRTypeKey(typet)), 
                        asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, this.getSpecialNothingType()),
                        trueflow: typet, 
                        falseflow: this.getSpecialNothingType() 
                    };
                }
                else {
                    //(option t)@nothing -- nothing, something(t), Nothing, Something<T>
                    return { 
                        asexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, this.getSpecialNothingType()),
                        asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, somethingtype),
                        trueflow: this.getSpecialNothingType(), 
                        falseflow: somethingtype 
                    };
                }
            }
            else {
                if (isnot) {
                    //(option t)@!nothing -- t, nothing, T, Nothing
                    return {
                        asexp: new TIRExtractExpression(sinfo, new TIRAsSomethingSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(somethingtype)), this.toTIRTypeKey(typet)),
                        asnotexp: new TIRAsNothingSpecialExpression(sinfo, tirexp),
                        trueflow: typet,
                        falseflow: this.getSpecialNothingType()
                    };
                }
                else {
                    //(option t)@nothing -- nothing, something(t), Nothing, Something<T>
                    return {
                        asexp: new TIRAsNothingSpecialExpression(sinfo, tirexp),
                        asnotexp: new TIRAsSomethingSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(somethingtype)),
                        trueflow: this.getSpecialNothingType(),
                        falseflow: somethingtype
                    };
                }
            }
        }
    }

    private processITestAsConvert_Something(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        this.raiseErrorIf(sinfo, !flowtype.isOptionType() && !flowtype.isSomethingType() && !flowtype.isNothingType(), "Special something test is only valid on Option<T> types (not part of a union etc.)");
        if (flowtype.isNothingType()) {
            if (isnot) {
                //(nothing)@!something -- nothing, x, Nothing, x
                return {
                    asexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, this.getSpecialNothingType()),
                    asnotexp: undefined,
                    trueflow: this.getSpecialNothingType(),
                    falseflow: undefined
                };
            }
            else {
                //(nothing)@something -- x, nothing, x, Nothing
                return {
                    asexp: undefined,
                    asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, this.getSpecialNothingType()),
                    trueflow: undefined,
                    falseflow: this.getSpecialNothingType()
                };
            }
        }
        else if(flowtype.isSomethingType()) {
            const typet = (flowtype.options[0] as ResolvedSomethingEntityAtomType).typeT;
            if (isnot) {
                //(something(t))@!something -- x, something(t), x, Something<T>
                return {
                    asexp: undefined,
                    asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, flowtype),
                    trueflow: undefined,
                    falseflow: flowtype
                };
            }
            else {
                //(something(t))@somethng -- t, x, T, x
                return {
                    asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, flowtype), this.toTIRTypeKey(typet)),
                    asnotexp: undefined,
                    trueflow: typet,
                    falseflow: undefined
                };
            }
        }
        else {
            const binds = (flowtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
            const typet = binds.get("T") as ResolvedType;
            const somethingtype = this.getSomethingType(typet);

            if (issafe) {
                if (isnot) {
                    //(option t)@!something -- nothing, something(t), Nothing, Something<T>
                    return { 
                        asexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, this.getSpecialNothingType()),
                        asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, somethingtype),
                        trueflow: this.getSpecialNothingType(), 
                        falseflow: somethingtype
                    };
                }
                else {
                    //(option t)@something -- t, nothing, T, Nothing
                    return { 
                        asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, somethingtype), this.toTIRTypeKey(typet)), 
                        asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, this.getSpecialNothingType()),
                        trueflow: typet, 
                        falseflow: this.getSpecialNothingType() 
                    };
                }
            }
            else {
                if (isnot) {
                    //(option t)@!something -- nothing, something(t), Nothing, Something<T>
                    return { 
                        asexp: new TIRAsNothingSpecialExpression(sinfo, tirexp),
                        asnotexp: new TIRAsSomethingSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(somethingtype)),
                        trueflow: this.getSpecialNothingType(), 
                        falseflow: somethingtype
                    };
                }
                else {
                    //(option t)@something -- t, nothing, T, Nothing
                    return { 
                        asexp: new TIRExtractExpression(sinfo, new TIRAsSomethingSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(somethingtype)), this.toTIRTypeKey(typet)), 
                        asnotexp: new TIRAsNothingSpecialExpression(sinfo, tirexp),
                        trueflow: typet, 
                        falseflow: this.getSpecialNothingType() 
                    };
                }
            }
        }
    }

    private processITestAsConvert_Ok(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        this.raiseErrorIf(sinfo, !flowtype.isOkType() && !flowtype.isErrType() && !flowtype.isResultType(), "Special ok test is only valid on Result<T, E> types (not part of a union etc.)");
        if (flowtype.isErrType()) {
            const typet = (flowtype.options[0] as ResolvedErrEntityAtomType).typeT;
            const typee = (flowtype.options[0] as ResolvedErrEntityAtomType).typeE;
            const errtype = this.getErrType(typet, typee);
        
            if (isnot) {
                //(err(e))@!ok -- e, x, E, x
                return {
                    asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, errtype), this.toTIRTypeKey(typee)),
                    asnotexp: undefined,
                    trueflow: typee,
                    falseflow: undefined
                };
            }
            else {
                //(err)@ok -- x, err, x, Err
                return {
                    asexp: undefined,
                    asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, errtype),
                    trueflow: undefined,
                    falseflow: errtype
                };
            }
        }
        else if(flowtype.isOkType()) {
            const typet = (flowtype.options[0] as ResolvedOkEntityAtomType).typeT;
            const typee = (flowtype.options[0] as ResolvedOkEntityAtomType).typeE;
            const oktype = this.getOkType(typet, typee);

            if (isnot) {
                //(ok(t))@!ok -- x, ok(t), x, Ok<T>
                return {
                    asexp: undefined,
                    asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, oktype),
                    trueflow: undefined,
                    falseflow: oktype
                };
            }
            else {
                //(ok(t))@ok -- t, x, T, x
                return {
                    asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, oktype), this.toTIRTypeKey(typet)),
                    asnotexp: undefined,
                    trueflow: typet,
                    falseflow: undefined
                };
            }
        }
        else {
            const binds = (flowtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
            const oktype = this.getOkType(binds.get("T") as ResolvedType, binds.get("E") as ResolvedType);
            const errtype = this.getErrType(binds.get("T") as ResolvedType, binds.get("E") as ResolvedType);

            const typet = binds.get("T") as ResolvedType;
            const typee = binds.get("E") as ResolvedType;

            if (issafe) {
                if (isnot) {
                    //result(t, e)@!ok -- e, ok(t), E, Ok<T>
                    return { 
                        asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, errtype), this.toTIRTypeKey(typee)),
                        asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, oktype),
                        trueflow: typee, 
                        falseflow: oktype 
                    };
                }
                else {
                    //result(t, e)@ok -- t, err(e), T, Err<E>
                    return { 
                        asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, oktype), this.toTIRTypeKey(typet)),
                        asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, errtype),
                        trueflow: typet, 
                        falseflow: errtype 
                    };
                }
            }
            else {
                if (isnot) {
                    //result(t, e)@!ok -- e, ok(t), E, Ok<T>
                    return { 
                        asexp: new TIRExtractExpression(sinfo, new TIRAsErrSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(errtype)), this.toTIRTypeKey(typee)),
                        asnotexp: new TIRAsOkSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(oktype)),
                        trueflow: typee, 
                        falseflow: oktype 
                    };
                }
                else {
                    //result(t, e)@ok -- t, err(e), T, Err<E>
                    return { 
                        asexp: new TIRExtractExpression(sinfo, new TIRAsOkSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(oktype)), this.toTIRTypeKey(typet)),
                        asnotexp: new TIRAsErrSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(errtype)),
                        trueflow: typet, 
                        falseflow: errtype 
                    };
                }
            }
        }
    }

    private processITestAsConvert_Err(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, isnot: boolean, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        this.raiseErrorIf(sinfo, !flowtype.isOkType() && !flowtype.isErrType() && !flowtype.isResultType(), "Special ok test is only valid on Result<T, E> types (not part of a union etc.)");
        if (flowtype.isErrType()) {
            const typet = (flowtype.options[0] as ResolvedErrEntityAtomType).typeT;
            const typee = (flowtype.options[0] as ResolvedErrEntityAtomType).typeE;
            const errtype = this.getErrType(typet, typee);
        
            if (isnot) {
                //(err(e))@!err -- x, err, x, Err
                return {
                    asexp: undefined,
                    asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, errtype),
                    trueflow: undefined,
                    falseflow: errtype
                };
            }
            else {
                //(err)@err -- e, x, E, x
                return {
                    asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, errtype), this.toTIRTypeKey(typee)),
                    asnotexp: undefined,
                    trueflow: typee,
                    falseflow: undefined
                };
            }
        }
        else if(flowtype.isOkType()) {
            const typet = (flowtype.options[0] as ResolvedOkEntityAtomType).typeT;
            const typee = (flowtype.options[0] as ResolvedOkEntityAtomType).typeE;
            const oktype = this.getOkType(typet, typee);

            if (isnot) {
                //(ok(t))@!err -- t, x, T, x
                return {
                    asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, oktype), this.toTIRTypeKey(typet)),
                    asnotexp: undefined,
                    trueflow: typet,
                    falseflow: undefined
                };
            }
            else {
                //(ok(t))@err -- x, ok(t), x, Ok<T>
                return {
                    asexp: undefined,
                    asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, oktype),
                    trueflow: undefined,
                    falseflow: oktype
                };
            }
        }
        else {
            const binds = (flowtype.options[0] as ResolvedConceptAtomType).conceptTypes[0].binds;
            const oktype = this.getOkType(binds.get("T") as ResolvedType, binds.get("E") as ResolvedType);
            const errtype = this.getErrType(binds.get("T") as ResolvedType, binds.get("E") as ResolvedType);

            const typet = binds.get("T") as ResolvedType;
            const typee = binds.get("E") as ResolvedType;

            if (issafe) {
                if (isnot) {
                    //result(t, e)@!err -- t, err(e), T, Err<E>
                    return { 
                        asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, oktype), this.toTIRTypeKey(typet)),
                        asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, errtype),
                        trueflow: typet, 
                        falseflow: errtype
                    };
                }
                else {
                    //result(t, e)@err -- e, ok(t), E, Ok<T>
                    return { 
                        asexp: new TIRExtractExpression(sinfo, this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, errtype), this.toTIRTypeKey(typee)),
                        asnotexp: this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, oktype),
                        trueflow: typee, 
                        falseflow: oktype 
                    };
                }
            }
            else {
                if (isnot) {
                    //result(t, e)@!err -- t, err(e), T, Err<E>
                    return { 
                        asexp: new TIRExtractExpression(sinfo, new TIRAsOkSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(oktype)), this.toTIRTypeKey(typet)),
                        asnotexp: new TIRAsErrSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(errtype)),
                        trueflow: typet, 
                        falseflow: errtype 
                    };
                }
                else {
                    //result(t, e)@err -- e, ok(t), E, Ok<T>
                    return { 
                        asexp: new TIRExtractExpression(sinfo, new TIRAsErrSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(errtype)), this.toTIRTypeKey(typee)),
                        asnotexp: new TIRAsOkSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(oktype)),
                        trueflow: typee, 
                        falseflow: oktype
                    };
                }
            }
        }
    }

    private processITestAsConvert_Literal(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, literal: LiteralExpressionValue, literaltype: ResolvedType, tirexp: TIRExpression, tirliteral: TIRLiteralValue, isnot: boolean, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        if (isnot) {
            let tptype: ResolvedType | undefined = undefined;
            let fptype: ResolvedType | undefined = undefined;

            if (literal.exp instanceof LiteralNoneExpression || literal.exp instanceof LiteralNothingExpression) {
                const tsplit = this.splitTypes(flowtype, literaltype);
                issafe = issafe || (isnot ? tsplit.tp === undefined : tsplit.fp === undefined);

                tptype = tsplit.fp;
                fptype = literaltype;
            }
            else {
                tptype = flowtype;
                fptype = flowtype;
            }

            if (issafe) {
                return { 
                    asexp: tptype !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tptype) : undefined,
                    asnotexp: fptype !==  undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, fptype) : undefined,
                    trueflow: tptype, 
                    falseflow: fptype 
                };
            }
            else {
                return { 
                    asexp: tptype !== undefined ? new TIRAsNotEqualToLiteralExpression(sinfo, tirexp, tirliteral, this.toTIRTypeKey(tptype)) : undefined, 
                    asnotexp: fptype !== undefined ? new TIRAsEqualToLiteralExpression(sinfo, tirexp, tirliteral, this.toTIRTypeKey(fptype)) : undefined,
                    trueflow: tptype, 
                    falseflow: fptype 
                };
            }
        }
        else {
            let tptype: ResolvedType | undefined = undefined;
            let fptype: ResolvedType | undefined = undefined;

            if (literal.exp instanceof LiteralNoneExpression || literal.exp instanceof LiteralNothingExpression) {
                const tsplit = this.splitTypes(flowtype, literaltype);
                issafe = issafe || (isnot ? tsplit.tp === undefined : tsplit.fp === undefined);

                tptype = literaltype;
                fptype = tsplit.fp;
            }
            else {
                tptype = flowtype;
                fptype = flowtype;
            }

            if (issafe) {
                return { 
                    asexp: tptype !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tptype) : undefined, 
                    asnotexp: fptype !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, fptype) : undefined, 
                    trueflow: tptype, 
                    falseflow: fptype 
                };
            }
            else {
                return { 
                    asexp: tptype !== undefined ? new TIRAsEqualToLiteralExpression(sinfo, tirexp, tirliteral, this.toTIRTypeKey(tptype)) : undefined, 
                    asnotexp: fptype !== undefined ? new TIRAsNotEqualToLiteralExpression(sinfo, tirexp, tirliteral, this.toTIRTypeKey(fptype)) : undefined, 
                    trueflow: tptype, 
                    falseflow: fptype 
                };
            }
        }
    }

    private processITestAsConvert_Type(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, intotype: ResolvedType, isnot: boolean, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        const tsplit = this.splitTypes(flowtype, intotype);
        issafe = issafe || (isnot ? tsplit.tp === undefined : tsplit.fp === undefined);

        if (isnot) {
            if(issafe) {
                return { 
                    asexp: tsplit.fp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.fp) : undefined,
                    asnotexp: tsplit.tp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.tp) : undefined,
                    trueflow: tsplit.fp, 
                    falseflow: tsplit.tp 
                };
            }

            if (intotype.options.length === 1 && ResolvedType.isUniqueType(intotype.options[0])) {
                if (intotype.isNoneType()) {
                    return { 
                        asexp: tsplit.fp !== undefined ? new TIRAsSomeSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp)) : undefined,
                        asnotexp: tsplit.tp !== undefined ? new TIRAsNoneSpecialExpression(sinfo, tirexp) : undefined,
                        trueflow: tsplit.fp, 
                        falseflow: tsplit.tp 
                    };
                }
                else if (intotype.isNothingType()) {
                    return { 
                        asexp: new TIRAsNothingSpecialExpression(sinfo, tirexp), 
                        asnotexp: new TIRAsNothingSpecialExpression(sinfo, tirexp),
                        trueflow: tsplit.fp, 
                        falseflow: tsplit.tp 
                    };
                }
                else {
                    return { 
                        asexp: tsplit.fp !== undefined ? new TIRAsNotTypeExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp), this.toTIRTypeKey(intotype)) : undefined,
                        asnotexp: tsplit.tp !== undefined ? new TIRAsTypeExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.tp), this.toTIRTypeKey(intotype)) : undefined,
                        trueflow: tsplit.fp, 
                        falseflow: tsplit.tp 
                    };
                }
            }
            else {
                if (intotype.isSomeType()) {
                    return { 
                        asexp: new TIRAsNoneSpecialExpression(sinfo, tirexp), 
                        asnotexp: tsplit.tp !== undefined ? new TIRAsSomeSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.tp)) : undefined, 
                        trueflow: tsplit.fp, 
                        falseflow: tsplit.tp 
                    };
                }
                else {
                    return { 
                        asexp: tsplit.fp !== undefined ? new TIRAsNotSubTypeExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp), this.toTIRTypeKey(intotype)) : undefined, 
                        asnotexp: tsplit.tp !== undefined ? new TIRAsSubTypeExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.tp), this.toTIRTypeKey(intotype)) : undefined,
                        trueflow: tsplit.fp, 
                        falseflow: tsplit.tp 
                    };
                }
            }
        }
        else {
            if (issafe) {
                return { 
                    asexp: tsplit.tp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.tp) : undefined, 
                    asnotexp: tsplit.fp !== undefined ? this.generateCoerceExpForITestConv(tirexp, ltype, sinfo, tsplit.fp) : undefined,
                    trueflow: tsplit.tp, 
                    falseflow: tsplit.fp 
                };
            }

            if (intotype.options.length === 1 && ResolvedType.isUniqueType(intotype.options[0])) {
                if (intotype.isNoneType()) {
                    return { 
                        asexp: new TIRAsNoneSpecialExpression(sinfo, tirexp), 
                        asnotexp: tsplit.fp !== undefined ? new TIRAsSomeSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp)) : undefined, 
                        trueflow: tsplit.tp, 
                        falseflow: tsplit.fp 
                    };
                }
                else if (intotype.isNothingType()) {
                    return { 
                        asexp: new TIRAsNothingSpecialExpression(sinfo, tirexp), 
                        asnotexp: new TIRAsNothingSpecialExpression(sinfo, tirexp),
                        trueflow: tsplit.tp, 
                        falseflow: tsplit.fp 
                    };
                }
                else {
                    return { 
                        asexp: tsplit.tp !== undefined ? new TIRAsTypeExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.tp), this.toTIRTypeKey(intotype)) : undefined,
                        asnotexp: tsplit.fp !== undefined ? new TIRAsNotTypeExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp), this.toTIRTypeKey(intotype)) : undefined,
                        trueflow: tsplit.tp, 
                        falseflow: tsplit.fp 
                    };
                }
            }
            else {
                if (intotype.isSomeType()) {
                    return { 
                        asexp: tsplit.fp !== undefined ? new TIRAsSomeSpecialExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp)) : undefined, 
                        asnotexp: new TIRAsNoneSpecialExpression(sinfo, tirexp),
                        trueflow: tsplit.tp, 
                        falseflow: tsplit.fp 
                    };
                }
                else {
                    return { 
                        asexp: tsplit.tp !== undefined ? new TIRAsSubTypeExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.tp), this.toTIRTypeKey(intotype)) : undefined, 
                        asnotexp: tsplit.fp !== undefined ? new TIRAsNotSubTypeExpression(sinfo, tirexp, this.toTIRTypeKey(tsplit.fp), this.toTIRTypeKey(intotype)) : undefined, 
                        trueflow: tsplit.tp, 
                        falseflow: tsplit.fp 
                    };
                }
            }
        }
    }

    private processITestAsConvertOp(sinfo: SourceInfo, ltype: ResolvedType, flowtype: ResolvedType, tirexp: TIRExpression, tt: ITest, binds: TemplateBindScope, issafe: boolean): { asexp: TIRExpression | undefined, asnotexp: TIRExpression | undefined, trueflow: ResolvedType | undefined, falseflow: ResolvedType | undefined } {
        if(tt instanceof ITestType) {
            const intotype = this.normalizeTypeOnly(tt.ttype, binds);
            return this.processITestAsConvert_Type(sinfo, ltype, flowtype, tirexp, intotype, tt.isnot, issafe);
        }
        else if(tt instanceof ITestLiteral) {
            const [tirliteral, ltype] = this.reduceLiteralValueToCanonicalForm(tt.literal.exp, binds);
            this.raiseErrorIf(sinfo, tirliteral === undefined, `could not evaluate literal value`);

            return this.processITestAsConvert_Literal(sinfo, ltype, flowtype, tt.literal, ltype, tirexp, tirliteral as TIRLiteralValue, tt.isnot, issafe);
        }
        else {
            if(tt instanceof ITestNone) {
                return this.processITestAsConvert_None(sinfo, ltype, flowtype, tirexp, tt.isnot, issafe);
            }
            else if(tt instanceof ITestSome) {
                return this.processITestAsConvert_Some(sinfo, ltype, flowtype, tirexp, tt.isnot, issafe);
            }
            else if(tt instanceof ITestNothing) {
                return this.processITestAsConvert_Nothing(sinfo, ltype, flowtype, tirexp, tt.isnot, issafe);
            }
            else if(tt instanceof ITestSomething) {
                return this.processITestAsConvert_Something(sinfo, ltype, flowtype, tirexp, tt.isnot, issafe);
            }
            else if(tt instanceof ITestOk) {
                return this.processITestAsConvert_Ok(sinfo, ltype, flowtype, tirexp, tt.isnot, issafe);
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                return this.processITestAsConvert_Err(sinfo, ltype, flowtype, tirexp, tt.isnot, issafe);
            }
        }
    }

    getDerivedTypeProjection(fromtype: ResolvedType, oftype: ResolvedType): ResolvedType | undefined {
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
                this.checkTemplateTypesOnType(t.sinfo, fconcept.terms, t.terms, binds);
                const bbinds = this.resolveTemplateBinds(t.sinfo, fconcept.terms, t.terms, binds);

                rtype = ResolvedType.createSingle(ResolvedConceptAtomType.create([ResolvedConceptAtomTypeEntry.create(fconcept, bbinds)]));
            }

            const fobject = this.m_assembly.tryGetObjectTypeForFullyResolvedName(ttname);
            if (fobject !== undefined) {
                let rtypeatom: ResolvedEntityAtomType | undefined = undefined;

                this.checkTemplateTypesOnType(t.sinfo, fobject.terms, t.terms, binds);
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
                this.checkTemplateTypesOnType(t.sinfo, ftask.terms, t.terms, binds);
                const bbinds = this.resolveTemplateBinds(t.sinfo, ftask.terms, t.terms, binds);

                rtype = ResolvedType.createSingle(ResolvedTaskAtomType.create(ftask, bbinds));
            }
        }

        if(isresolution) {
            let sstr = (t.nameSpace !== "Core" ? (t.nameSpace + "::") : "") + t.computeResolvedName();
            assert(t.terms.length === 0, "typedefs should not have templates");

            this.m_typedefResolutions.set(sstr, rtype as ResolvedType);
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

    private normalizeType_Projection(t: ProjectTypeSignature, binds: TemplateBindScope): ResolvedType {
        const fromt = this.normalizeTypeOnly(t.fromtype, binds);
        const oft = this.normalizeTypeOnly(t.oftype, binds);

        if(fromt.isInvalidType() || oft.isInvalidType()) {
            return ResolvedType.createInvalid();
        }

        return this.getDerivedTypeProjection(fromt, oft) || ResolvedType.createInvalid();
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

        return this.normalizeAndList(itypes);
    }

    private normalizeType_Union(t: UnionTypeSignature, binds: TemplateBindScope): ResolvedType {
        const uniontypes = t.types.map((opt) => this.normalizeTypeOnly(opt, binds));

        if (uniontypes.some((opt) => opt.isInvalidType())) {
            return ResolvedType.createInvalid();
        }

        return this.normalizeUnionList(uniontypes);
    }

    private normalizeAndList(itypes: ResolvedConceptAtomTypeEntry[]): ResolvedType {
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

        const utypes = flattened.sort((cte1, cte2) => cte1.typeID.localeCompare(cte2.typeID));

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

        if (ttype.tryGetUniqueEntityTypeInfo() instanceof ResolvedTypedeclEntityAtomType) {
            const ccdecl = ttype.tryGetUniqueEntityTypeInfo() as ResolvedTypedeclEntityAtomType;
            const oftype = ResolvedType.createSingle(ccdecl.valuetype);

            declinvs = this.getAllInvariantProvidingTypesTypedecl(oftype, ccdecl.valuetype.object, ccdecl.valuetype.getBinds(), declinvs);
        }

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
        const ccdecls = this.getAllInvariantProvidingTypesTypedecl(ttype, ooptype, new Map<string, ResolvedType>());
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

    private isExportable(rtype: ResolvedAtomType): boolean {
        if(ResolvedType.isUniversalConceptType(rtype)) {
            return false;
        }

        return this.subtypeOf(ResolvedType.createSingle(rtype), this.m_istestbuild ? this.getSpecialTestableTypeConceptType() : this.getSpecialAPITypeConceptType());
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
        const isexportable = this.isExportable(rtype);
        if(rtype instanceof ResolvedObjectEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, rtype.object.terms.map((term) => this.toTIRTypeKey(rtype.binds.get(term.name) as ResolvedType)));
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createBaseBindScope(rtype.binds)).map((rr) => this.toTIRTypeKey(rr));
           
            const binds = new Map<string, TIRTypeKey>();
            rtype.binds.forEach((rt, tt) => binds.set(tt, this.toTIRTypeKey(rt)));

            tirtype = new TIRObjectEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, binds, isexportable);
            this.m_pendingEntityDecls.push({tirtype: tirtype as TIRObjectEntityType, rtype: rtype, tdecl: rtype.object, binds: rtype.getBinds()});
            this.m_instantiatedVTableTypes.push(rtype);
        }
        else if(rtype instanceof ResolvedEnumEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));
            const enums = rtype.object.staticMembers.map((sm) => sm.name);

            tirtype = new TIREnumEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, enums);
            this.m_pendingEnumDecls.push({tirtype: tirtype as TIREnumEntityType, rtype: rtype, tdecl: rtype.object, binds: new Map<string, ResolvedType>()});
        }
        else if(rtype instanceof ResolvedTypedeclEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));

            const valuetype = this.toTIRTypeKey(ResolvedType.createSingle(rtype.valuetype));
            const representation = this.toTIRTypeKey(ResolvedType.createSingle(rtype.representation));

            const invdecls = this.getAllInvariantProvidingTypesTypedecl(ResolvedType.createSingle(rtype), rtype.object, new Map<string, ResolvedType>());
            const validators = this.toTIRTypedeclChecks(ResolvedType.createSingle(rtype), invdecls);

            const strof = validators.strof !== undefined ? ({vtype: validators.strof.typeID, vre: this.processValidatorRegex(rtype.object.sourceLocation, validators.strof.typeID)}) : undefined;
            const pthof = validators.pthof !== undefined ? ({vtype: validators.pthof.validator.typeID, vpth: this.m_assembly.tryGetPathValidatorForFullyResolvedName(validators.pthof.validator.typeID) as PathValidator, kind: validators.pthof.kind}) : undefined;

            const iskeytype = this.subtypeOf(ResolvedType.createSingle(ResolvedType.createSingle(rtype.representation)), this.getSpecialKeyTypeConceptType());

            tirtype = new TIRTypedeclEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, valuetype, representation, strof, pthof, iskeytype, isexportable);
            this.m_pendingTypedeclDecls.push({tirtype: tirtype as TIRTypedeclEntityType, rtype: rtype, tdecl: rtype.object, binds: rtype.getBinds()});
        }
        else if(rtype instanceof ResolvedPrimitiveInternalEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));
            const iskeytype = this.subtypeOf(ResolvedType.createSingle(rtype), this.getSpecialKeyTypeConceptType());

            tirtype = new TIRPrimitiveInternalEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, iskeytype);
        }
        else if(rtype instanceof ResolvedValidatorEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createEmptyBindScope()).map((rr) => this.toTIRTypeKey(rr));

            tirtype = new TIRValidatorEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, this.processValidatorRegex(rtype.object.sourceLocation, rtype.typeID));
        }
        else if(rtype instanceof ResolvedStringOfEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));            
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));

            const revalidator = this.processValidatorRegex(rtype.object.sourceLocation, rtype.validatortype.typeID);
            
            tirtype = new TIRStringOfEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, validator, revalidator);
        }
        else if(rtype instanceof ResolvedASCIIStringOfEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));

            const revalidator = this.processValidatorRegex(rtype.object.sourceLocation, rtype.validatortype.typeID);
            
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
            const typet = this.toTIRTypeKey(rtype.typeT);
            const typee = this.toTIRTypeKey(rtype.typeE);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet, typee]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createDoubleBindScope("T", rtype.typeT, "E", rtype.typeE)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIROkEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, typee, isexportable);
        }
        else if(rtype instanceof ResolvedErrEntityAtomType) {
            const typet = this.toTIRTypeKey(rtype.typeT);
            const typee = this.toTIRTypeKey(rtype.typeE);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet, typee]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createDoubleBindScope("T", rtype.typeT, "E", rtype.typeE)).map((rr) => this.toTIRTypeKey(rr));

            tirtype = new TIRErrEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, typee, isexportable);
        }
        else if(rtype instanceof ResolvedSomethingEntityAtomType) {
            const typet = this.toTIRTypeKey(rtype.typeT);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRSomethingEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, isexportable);
        }
        else if(rtype instanceof ResolvedMapEntryEntityAtomType) {
            const typet = this.toTIRTypeKey(rtype.typeK);
            const typee = this.toTIRTypeKey(rtype.typeV);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet, typee]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createDoubleBindScope("K", rtype.typeK, "V", rtype.typeV)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRMapEntryEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, typee, isexportable);
        }
        else if(rtype instanceof ResolvedHavocEntityAtomType) {
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, undefined);
            tirtype = new TIRHavocEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes);
        }
        else if(rtype instanceof ResolvedListEntityAtomType) {
            const typet = this.toTIRTypeKey(rtype.typeT);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRListEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, isexportable);
        }
        else if(rtype instanceof ResolvedStackEntityAtomType) {
            const typet = this.toTIRTypeKey(rtype.typeT);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRStackEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, isexportable);
        }
        else if(rtype instanceof ResolvedQueueEntityAtomType) {
            const typet = this.toTIRTypeKey(rtype.typeT);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRQueueEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, isexportable);
        }
        else if(rtype instanceof ResolvedSetEntityAtomType) {
            const typet = this.toTIRTypeKey(rtype.typeT);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typet]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", rtype.typeT)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRSetEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typet, isexportable);
        }
        else if(rtype instanceof ResolvedMapEntityAtomType) {
            const typek = this.toTIRTypeKey(rtype.typeK);
            const typev = this.toTIRTypeKey(rtype.typeV);
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [typek, typev]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createDoubleBindScope("K", rtype.typeK, "V", rtype.typeV)).map((rr) => this.toTIRTypeKey(rr));
            
            tirtype = new TIRMapEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typek, typev, isexportable);
        }
        else if(rtype instanceof ResolvedConceptAtomType) {
            if(rtype.conceptTypes.length === 1) {
                const rconcept = rtype.conceptTypes[0];
                const tname = new TIRTypeName(rconcept.concept.ns, rconcept.concept.name, rconcept.concept.terms.map((term) => this.toTIRTypeKey(rconcept.binds.get(term.name) as ResolvedType)));
                const supertypes = this.resolveProvides(rconcept.concept, TemplateBindScope.createBaseBindScope(rconcept.binds)).map((rr) => this.toTIRTypeKey(rr));
                
                const binds = new Map<string, TIRTypeKey>();
                rconcept.binds.forEach((rt, tt) => binds.set(tt, this.toTIRTypeKey(rt)));

                tirtype = new TIRConceptType(rconcept.typeID, tname, rconcept.concept.sourceLocation, rconcept.concept.srcFile, rconcept.concept.attributes, supertypes, binds, isexportable);
                this.m_pendingConceptDecls.push({tirtype: tirtype as TIRConceptType, rtype: rtype.conceptTypes[0], tdecl: rtype.conceptTypes[0].concept, binds: rtype.conceptTypes[0].binds});
            }
            else {
                const tirconjuncts = rtype.conceptTypes.map((cpt) => {
                    return this.toTIRTypeKey(ResolvedType.createSingle(ResolvedConceptAtomType.create([cpt])));
                });

                tirtype = new TIRConceptSetType(rtype.typeID, tirconjuncts, isexportable);
            }
        }
        else if(rtype instanceof ResolvedTaskAtomType) {
            const tname = new TIRTypeName(rtype.task.ns, rtype.task.name, rtype.task.terms.map((term) => this.toTIRTypeKey(rtype.binds.get(term.name) as ResolvedType)));
            const supertypes = this.resolveProvides(rtype.task, TemplateBindScope.createBaseBindScope(rtype.binds)).map((rr) => this.toTIRTypeKey(rr));

            const binds = new Map<string, TIRTypeKey>();
            rtype.binds.forEach((rt, tt) => binds.set(tt, this.toTIRTypeKey(rt)));

            const mainfunc = {mkey: TIRIDGenerator.generateInvokeForMemberFunction(rtype.typeID, rtype.task.mainfunc.name, [], []), mname: rtype.task.mainfunc.name};
            const onfuncs = {
                onCanel: rtype.task.onfuncs.onCanel !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.onfuncs.onCanel.name, [], [])) : undefined, 
                onFailure: rtype.task.onfuncs.onFailure !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.onfuncs.onFailure.name, [], [])) : undefined, 
                onTimeout: rtype.task.onfuncs.onTimeout !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.onfuncs.onTimeout.name, [], [])) : undefined 
            };

            const lfuncs = {
                logStart: rtype.task.lfuncs.logStart !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.lfuncs.logStart.name, [], [])) : undefined, 
                logEnd: rtype.task.lfuncs.logEnd !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.lfuncs.logEnd.name, [], [])) : undefined, 
                taskEnsures: rtype.task.lfuncs.taskEnsures !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.lfuncs.taskEnsures.name, [], [])) : undefined, 
                taskWarns: rtype.task.lfuncs.taskWarns !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.lfuncs.taskWarns.name, [], [])) : undefined 
            };

            tirtype = new TIRTaskType(rtype.typeID, tname, rtype.task.sourceLocation, rtype.task.srcFile, rtype.task.attributes, supertypes, binds, mainfunc, onfuncs, lfuncs);
            this.m_pendingTaskDecls.push({tirtype: tirtype as TIRTaskType, rtype: rtype, tdecl: rtype.task, binds: new Map<string, ResolvedType>()});
        }
        else if(rtype instanceof ResolvedTupleAtomType) {
            const supertypes = this.getConceptsProvidedByTuple(rtype).conceptTypes.map((cc) => this.toTIRTypeKey(ResolvedType.createSingle(ResolvedConceptAtomType.create([cc]))));
            tirtype = new TIRTupleType(rtype.typeID, rtype.types.map((tt) => this.toTIRTypeKey(tt)), supertypes, isexportable);
        }
        else if(rtype instanceof ResolvedRecordAtomType) {
            const supertypes = this.getConceptsProvidedByRecord(rtype).conceptTypes.map((cc) => this.toTIRTypeKey(ResolvedType.createSingle(ResolvedConceptAtomType.create([cc]))));
            tirtype = new TIRRecordType(rtype.typeID, rtype.entries.map((entrey) => {
                return {pname: entrey.pname, ptype: this.toTIRTypeKey(entrey.ptype)};
            }), supertypes, isexportable);
        }
        else {
            assert(false, `Unknown type to convert ${rtype.typeID}`);
            tirtype = (undefined as any) as TIRType;
        }

        if(tirtype instanceof TIROOType) {
            const nsdecl = this.m_tirNamespaceMap.get(tirtype.tname.ns) as TIRNamespaceDeclaration;

            if (tirtype instanceof TIRTaskType) {
                nsdecl.tasks.set(tirtype.tname.name, tirtype.tkey);
            }
            else if (tirtype instanceof TIRConceptType) {
                if(!nsdecl.concepts.has(tirtype.tname.name)) {
                    nsdecl.concepts.set(tirtype.tname.name, []);
                }
                (nsdecl.concepts.get(tirtype.tname.name) as TIRTypeKey[]).push(tirtype.tkey);
            }
            else {
                if(!nsdecl.objects.has(tirtype.tname.name)) {
                    nsdecl.objects.set(tirtype.tname.name, []);
                }
                (nsdecl.objects.get(tirtype.tname.name) as TIRTypeKey[]).push(tirtype.tkey);
            }
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
            const isexportable = rtype.options.every((opt) => this.isExportable(opt));
            const tt = new TIRUnionType(rtype.typeID, opts, isexportable);
            
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

    getSpecialTestableTypeConceptType(): ResolvedType { return this.internSpecialConceptType("Testable"); }
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

        if (options.includes(ResolveResultFlag.notfound)) {
            if (mdecl !== undefined && !mdecl.hasAttribute("override")) {
                return [new OOMemberLookupInfo<T>(ttype, ooptype, oobinds, mdecl)];
            }
        }

        const ropts = options.filter((opt) => opt !== ResolveResultFlag.failure && opt !== ResolveResultFlag.notfound) as OOMemberLookupInfo<T>[][];
        if(ropts.length === 0) {
            return ResolveResultFlag.notfound;
        }

        let decls: OOMemberLookupInfo<T>[] = [];
        for(let i = 0; i < ropts.length; ++i) {
            const newopts = ropts[i].filter((opt) => !decls.some((info) => info.ttype.typeID === opt.ttype.typeID));
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

        if (decls.length === 0) {
            this.raiseError(sinfo, `Missing declaraton for ${name} on type ${atom.typeID}`);
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
            const newopts = (implopts[i] as OOMemberLookupInfo<T>[]).filter((opt) => !impls.some((info) => info.ttype.typeID === opt.ttype.typeID));
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

        if (decls.length === 0) {
            this.raiseError(sinfo, `Missing declaraton for ${name} on type ${atom.typeID}`);
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

        if (decls.length === 0) {
            this.raiseError(sinfo, `Missing declaraton for ${name} on type ${atom.typeID}`);
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

        return new OOMemberResolution<T>(decls[0], impls, totalresolve);
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

        this.raiseErrorIf(t.sinfo, (res instanceof ResolvedFunctionType), `Function type not expected here -- got ${t.getDiagnosticName()}`);
        this.raiseErrorIf(t.sinfo, res.typeID === "[INVALID]", `Type ${t.getDiagnosticName()} is invalid`);

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
                this.raiseError(tt.sourceLocation, `provides types must be a concept -- got ${rsig.typeID}`);
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

        this.raiseErrorIf(sinfo, !this.subtypeOf(env.trepr, trgttype), `Cannot convert type ${env.trepr.typeID} into ${trgttype.typeID}`);
        return env.setResultExpressionInfo(new TIRCoerceSafeExpression(sinfo, env.expressionResult, this.toTIRTypeKey(env.trepr), this.toTIRTypeKey(trgttype)), trgttype);
    }

    private emitCoerceIfNeeded_NoCheck(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        return env.setResultExpressionInfo(new TIRCoerceSafeExpression(sinfo, env.expressionResult, this.toTIRTypeKey(env.trepr), this.toTIRTypeKey(trgttype)), trgttype);
    }

    private generateCoerceExpForITestConv(exp: TIRExpression, oftype: ResolvedType, sinfo: SourceInfo, trgttype: ResolvedType): TIRExpression {
        if(oftype.isSameType(trgttype)) {
            return exp;
        }

        return new TIRCoerceSafeExpression(sinfo, exp, this.toTIRTypeKey(oftype), this.toTIRTypeKey(trgttype));
    }

    private checkTemplateTypesOnType(sinfo: SourceInfo, terms: TemplateTermDecl[], giventerms: TypeSignature[], typescope: TemplateBindScope) {
        for(let i = 0; i < terms.length; ++i) {
            const terminfo = terms[i];
            const termtype = this.normalizeTypeOnly(giventerms[i], typescope);

            const termconstraint = this.normalizeTypeOnly(terminfo.tconstraint, TemplateBindScope.createEmptyBindScope());
            const boundsok = this.subtypeOf(termtype, termconstraint);
            this.raiseErrorIf(sinfo, !boundsok, `Template instantiation does not satisfy specified bounds -- not subtype of ${termconstraint.typeID}`);

            if (terminfo.isunique) {
                this.raiseErrorIf(sinfo, termtype.options.length !== 1 || !ResolvedType.isUniqueType(termtype.options[0]), `Template type ${termtype.typeID} is not unique`);
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

    private isPCodeTypedExpression(e: Expression, env: ExpressionTypeEnvironment): boolean {
        if(e instanceof ConstructorPCodeExpression) {
            return true;
        }
        else if (e instanceof AccessVariableExpression) {
            return env.argpcodes.has(e.name) || env.capturedpcodes.has(e.name);
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
                if(lhs.options.length === 1 && ResolvedType.isUniqueType(lhs.options[0])) {
                    return "lhssomekeywithunique";
                }
                else {
                    return "lhssomekey";
                }
            }
            else {
                if(rhs.options.length === 1 && ResolvedType.isUniqueType(rhs.options[0])) {
                    return "rhssomekeywithunique";
                }
                else {
                    return "rhssomekey";
                }
            }
        }
    }

    private checkPCodeExpression(env: ExpressionTypeEnvironment, exp: ConstructorPCodeExpression, expectedFunction: ResolvedFunctionType): [TIRCreateCodePackExpression, ResolvedFunctionType] {
        this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");

        let bodybinds = new Map<string, ResolvedType>();
        exp.invoke.captureTemplateSet.forEach((ttname) => {
            bodybinds.set(ttname, env.binds.templateResolveType(ttname));
        });

        const ltypetry = exp.isAuto ? expectedFunction : this.normalizeTypeFunction(exp.invoke.generateSig(exp.invoke.startSourceLocation), env.binds);
        this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");
        const ltype = ltypetry as ResolvedFunctionType;

        this.raiseErrorIf(exp.sinfo, exp.invoke.params.length !== ltype.params.length, "Mismatch in expected parameter count and provided function parameter count");
        this.raiseErrorIf(exp.sinfo, expectedFunction !== undefined && !this.functionSubtypeOf(ltype, expectedFunction), "Mismatch in expected and provided function signature");

        let captures: string[] = [];
        exp.invoke.captureVarSet.forEach((v) => captures.push(v));
        captures.sort();

        let capturedpcodes = new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>();
        let capturedvars = new Map<string, {vname: string, vtype: ResolvedType}>();

        let capturedirect: string[] = [];
        let captureindirect: string[] = [];
        let capturepackdirect: string[] = [];
        let capturepackindirect: string[] = [];

        captures.forEach((v) => {
            if(env.lookupLocalVar(v) !== null) {
                capturedirect.push(v);
                capturedvars.set(v, {vname: v, vtype: (env.lookupLocalVar(v) as VarInfo).declaredType});
            }
            else if(env.lookupCapturedVar(v) !== null) {
                captureindirect.push(v);
                capturedvars.set(v, {vname: v, vtype: (env.lookupLocalVar(v) as VarInfo).declaredType});
            }
            else if(env.lookupArgPCode(v) !== null) {
                capturepackdirect.push(v);
                capturedpcodes.set(v, (env.lookupArgPCode(v) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}));
            }
            else {
                capturepackindirect.push(v);
                capturedpcodes.set(v, (env.lookupCapturedPCode(v) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}));
            }
        });

        let argpcodes = new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>();
        expectedFunction.params.forEach((ff) => {
            if (ff.type instanceof ResolvedFunctionType) {
                argpcodes.set(ff.name, env.argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType});
            }
        });

        const pcterms = [...bodybinds].map((bb) => this.toTIRTypeKey(bb[1])).sort();
        const pclcaptures = [...capturedpcodes].map((pm) => pm[1].pcode.codekey).sort();

        const pcvarinfo = [...capturedvars].sort((a, b) => a[0].localeCompare(b[0])).map((cv) => { return {cname: cv[0], ctype: this.toTIRTypeKey(cv[1].vtype)}; });
        const pclinfo = [...capturedpcodes].sort((a, b) => a[0].localeCompare(b[0])).map((cv) => { return {cpname: cv[0], cpval: cv[1].pcode.codekey}; });

        const [lcodekey, linvkey] = TIRIDGenerator.generatePCodeIDInfoForLambda(this.m_file, exp.sinfo, this.m_lambdaCtr++, pcterms, pclcaptures);
        const cpack = new TIRCodePack(this.m_ns, lcodekey, linvkey, exp.invoke.recursive === "yes", pcterms, pclcaptures, pcvarinfo, pclinfo);

        this.m_pendingCodeDecls.push({cpdata: cpack, cpdecl: exp.invoke, desiredfunc: ltype, declbinds: env.binds, bodybinds: bodybinds, capturedpcodes: capturedpcodes, capturedvars: capturedvars, argpcodes: argpcodes});

        return [new TIRCreateCodePackExpression(exp.sinfo, cpack, lcodekey, capturedirect, captureindirect, capturepackdirect, capturepackindirect), ltype];
    }

    private checkArgumentList(sinfo: SourceInfo, env: ExpressionTypeEnvironment, args: Expression[], calleeparams: FunctionParameter[], fbinds: TemplateBindScope): [TIRExpression[], [string, ResolvedFunctionType, TIRCodePack][], TIRPCodeKey[]] {
        this.raiseErrorIf(sinfo, args.length !== calleeparams.length, `call expected ${calleeparams.length} arguments but got ${args.length}`);
        const eenvs = args.map((arg, ii) => {
            if (this.isPCodeTypedExpression(arg, env)) {
                const expectedfunc = this.normalizeTypeFunction(calleeparams[ii].type, fbinds);
                this.raiseErrorIf(sinfo, expectedfunc === undefined, `Expected function argument but got ${calleeparams[ii].type.getDiagnosticName()}`);

                if(arg instanceof AccessVariableExpression) {
                    const pcl = env.lookupArgPCode(arg.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType};
                    return [calleeparams[ii].name, new TIRAccessVariableExpression(arg.sinfo, arg.name, pcl.pcode.codekey), pcl.pcode, expectedfunc as ResolvedFunctionType] as [string, TIRExpression, TIRCodePack, ResolvedFunctionType];
                }
                else {
                    const pcl = this.checkPCodeExpression(env, arg as ConstructorPCodeExpression, expectedfunc as ResolvedFunctionType);
                    return [calleeparams[ii].name, pcl[0], pcl[0].pcodepack, pcl[1]] as [string, TIRExpression, TIRCodePack, ResolvedFunctionType];
                }   
            }
            else {
                return this.checkExpression(env, arg, this.normalizeTypeOnly(calleeparams[ii].type, fbinds));
            }
        });

        let cexps: TIRExpression[] = [];
        let ftypes: [string, ResolvedFunctionType, TIRCodePack][] = [];
        let pckeys: TIRPCodeKey[] = [];
        for (let i = 0; i < eenvs.length; ++i) {
            const oftype = this.normalizeTypeGeneral(calleeparams[i].type, fbinds);

            if (Array.isArray(eenvs[i])) {
                const eev = eenvs[i] as [string, TIRExpression, TIRCodePack, ResolvedFunctionType];

                cexps.push(eev[1]);
                ftypes.push([eev[0], eev[3], eev[2]]);
                pckeys.push(eev[2].codekey);
            }
            else {
                assert(oftype instanceof ResolvedType, "Something went wrong");
                this.raiseErrorIf(args[i].sinfo, !this.subtypeOf((eenvs[i] as ExpressionTypeEnvironment).trepr, oftype as ResolvedType), `${(eenvs[i] as ExpressionTypeEnvironment).trepr.typeID} is not a subtype of ${oftype.typeID}`);

                cexps.push(this.emitCoerceIfNeeded(eenvs[i] as ExpressionTypeEnvironment, args[i].sinfo, oftype as ResolvedType).expressionResult);
            }
        }

        return [cexps, ftypes, pckeys];
    }

    private checkLiteralNoneExpression(env: ExpressionTypeEnvironment, exp: LiteralNoneExpression): ExpressionTypeEnvironment {
        return  env.setResultExpressionInfo(new TIRLiteralNoneExpression(exp.sinfo), this.getSpecialNoneType());
    }

    private checkLiteralNothingExpression(env: ExpressionTypeEnvironment, exp: LiteralNothingExpression): ExpressionTypeEnvironment {
        return env.setResultExpressionInfo(new TIRLiteralNothingExpression(exp.sinfo), this.getSpecialNothingType());
    }

    private checkLiteralBoolExpression(env: ExpressionTypeEnvironment, exp: LiteralBoolExpression): ExpressionTypeEnvironment {
        return env.setResultExpressionInfo(new TIRLiteralBoolExpression(exp.sinfo, exp.value), this.getSpecialBoolType());
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

        return env.setResultExpressionInfo(new TIRLiteralIntegralExpression(exp.sinfo, exp.value, this.toTIRTypeKey(itype)), itype);
    }

    private checkLiteralRationalExpression(env: ExpressionTypeEnvironment, exp: LiteralRationalExpression): ExpressionTypeEnvironment {
        //TODO: range check here
        return env.setResultExpressionInfo(new TIRLiteralRationalExpression(exp.sinfo, exp.value), this.getSpecialRationalType());
    } 

    private checkLiteralFloatExpression(env: ExpressionTypeEnvironment, exp: LiteralFloatPointExpression): ExpressionTypeEnvironment {
        const fptype = this.normalizeTypeOnly(exp.fptype, env.binds);

        //TODO: range check here
        return env.setResultExpressionInfo(new TIRLiteralFloatPointExpression(exp.sinfo, exp.value, this.toTIRTypeKey(fptype)), fptype);
    }

    private checkLiteralStringExpression(env: ExpressionTypeEnvironment, exp: LiteralStringExpression): ExpressionTypeEnvironment {
        return env.setResultExpressionInfo(new TIRLiteralStringExpression(exp.sinfo, exp.value), this.getSpecialStringType());
    }

    private checkLiteralASCIIStringExpression(env: ExpressionTypeEnvironment, exp: LiteralASCIIStringExpression): ExpressionTypeEnvironment {
        return env.setResultExpressionInfo(new TIRLiteralASCIIStringExpression(exp.sinfo, exp.value), this.getSpecialASCIIStringType());
     }

    private checkLiteralRegexExpression(env: ExpressionTypeEnvironment, exp: LiteralRegexExpression): ExpressionTypeEnvironment {
        return env.setResultExpressionInfo(new TIRLiteralRegexExpression(exp.sinfo, exp.value), this.getSpecialRegexType());
    }

    private checkLiteralTypedStringExpression(env: ExpressionTypeEnvironment, exp: LiteralTypedStringExpression): ExpressionTypeEnvironment {
        const toftype = this.normalizeTypeOnly(exp.stype, env.binds);
        this.raiseErrorIf(exp.sinfo, !(toftype.tryGetUniqueEntityTypeInfo() instanceof ResolvedValidatorEntityAtomType), `Expected Validator for StringOf but got ${toftype.typeID}`);

        const vtype = toftype.tryGetUniqueEntityTypeInfo() as ResolvedValidatorEntityAtomType;
        const stype = ResolvedType.createSingle(ResolvedStringOfEntityAtomType.create(this.m_assembly.getNamespace("Core").objects.get("StringOf") as EntityTypeDecl, vtype));

        const vv = this.processValidatorRegex(exp.sinfo, toftype.typeID);
        this.raiseErrorIf(exp.sinfo, vv === undefined, `Bad Validator type for StringOf ${toftype.typeID}`);
            
        const argstr = extractLiteralStringValue(exp.value);
        const accepts = (vv as BSQRegex).acceptsString(argstr);
        
        this.raiseErrorIf(exp.sinfo, !accepts, "Literal string failed Validator regex");

        return env.setResultExpressionInfo(new TIRLiteralTypedStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(stype), this.toTIRTypeKey(toftype)), stype);
    }

    private checkLiteralASCIITypedStringExpression(env: ExpressionTypeEnvironment, exp: LiteralASCIITypedStringExpression): ExpressionTypeEnvironment {
        const toftype = this.normalizeTypeOnly(exp.stype, env.binds);
        this.raiseErrorIf(exp.sinfo, !(toftype.tryGetUniqueEntityTypeInfo() instanceof ResolvedValidatorEntityAtomType), `Expected Validator for StringOf but got ${toftype.typeID}`);

        const vtype = toftype.tryGetUniqueEntityTypeInfo() as ResolvedValidatorEntityAtomType;
        const stype = ResolvedType.createSingle(ResolvedStringOfEntityAtomType.create(this.m_assembly.getNamespace("Core").objects.get("ASCIIStringOf") as EntityTypeDecl, vtype));

        const vv = this.processValidatorRegex(exp.sinfo, toftype.typeID);
        this.raiseErrorIf(exp.sinfo, vv === undefined, `Bad Validator type for StringOf ${toftype.typeID}`);
            
        const argstr = extractLiteralASCIIStringValue(exp.value);
        const accepts = (vv as BSQRegex).acceptsString(argstr);
        
        this.raiseErrorIf(exp.sinfo, !accepts, "Literal string failed Validator regex");

        return env.setResultExpressionInfo(new TIRLiteralASCIITypedStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(stype), this.toTIRTypeKey(toftype)), stype);
    }

    private checkLiteralTemplateStringExpression(env: ExpressionTypeEnvironment, exp: LiteralTemplateStringExpression): ExpressionTypeEnvironment {
        //
        //TODO: maybe generate special TemplateString<T, K> ... types for these later -- right now we just expect them to be compile inlined
        //
        return env.setResultExpressionInfo(new TIRLiteralTemplateStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(this.getSpecialStringType())), this.getSpecialStringType());
    }

    private checkLiteralASCIITemplateStringExpression(env: ExpressionTypeEnvironment, exp: LiteralASCIITemplateStringExpression): ExpressionTypeEnvironment {
        //
        //TODO: maybe generate special TemplateString<T, K> ... types for these later -- right now we just expect them to be compile inlined
        //
        return env.setResultExpressionInfo(new TIRLiteralASCIITemplateStringExpression(exp.sinfo, exp.value, this.toTIRTypeKey(this.getSpecialASCIIStringType())), this.getSpecialASCIIStringType());
    }

    private checkLiteralTypedPrimitiveConstructorExpression(env: ExpressionTypeEnvironment, exp: LiteralTypedPrimitiveConstructorExpression): ExpressionTypeEnvironment {
        const constype = this.normalizeTypeOnly(exp.constype, env.binds);
        const lexp = this.reduceLiteralValueToCanonicalForm(exp.value, env.binds);
        this.raiseErrorIf(exp.sinfo, lexp === undefined, "Not a literal expression");

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
            return env.setResultExpressionInfo(nexp, constype);
        }
        else {
            const nexp = new TIRLiteralTypedPrimitiveConstructorExpression(exp.sinfo, (lexp[0] as TIRLiteralValue).exp, this.toTIRTypeKey(constype), this.toTIRTypeKey(ResolvedType.createSingle(ccdecl.representation)));
            return env.setResultExpressionInfo(nexp, constype);
        }
    }

    private checkAccessFormatInfo(env: ExpressionTypeEnvironment, exp: AccessFormatInfoExpression): ExpressionTypeEnvironment {
        assert(false, "TODO: maybe this is ok for string formats but right now this shouldn't happen");

        return env;
    }

    private checkAccessEnvValue(env: ExpressionTypeEnvironment, exp: AccessEnvValueExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk !== "write", `Can only access "environment" variables in task actions`);

        const valtype = this.normalizeTypeOnly(exp.valtype, env.binds);
        const restype = this.normalizeTypeOnly(new UnionTypeSignature(exp.sinfo, [exp.valtype, new NominalTypeSignature(exp.sinfo, "Core", ["None"])]), env.binds);

        return env.setResultExpressionInfo(new TIRAccessEnvValueExpression(exp.sinfo, exp.keyname, this.toTIRTypeKey(valtype), this.toTIRTypeKey(restype), exp.orNoneMode), restype);
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
            return this.emitCoerceIfNeeded(this.checkExpression(env, cexp, rtype), exp.sinfo, rtype);
        }
        else {
            const tirrtype = this.toTIRTypeKey(rtype);

            this.m_pendingNamespaceConsts.push(cdecl);
            return env.setResultExpressionInfo(new TIRAccessNamespaceConstantExpression(exp.sinfo, exp.ns, exp.name, tirrtype), rtype);
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
            return this.emitCoerceIfNeeded(this.checkExpression(env, cexp, rtype), exp.sinfo, rtype);
        }
        else {
            const tirdecltype = this.toTIRTypeKey(cdecl.ttype);
            const tirrtype = this.toTIRTypeKey(rtype);

            this.m_pendingConstMemberDecls.push(cdecl);
            return env.setResultExpressionInfo(new TIRAccessConstMemberFieldExpression(exp.sinfo, tirdecltype, exp.name, tirrtype), rtype);
        }
    }

    private checkAccessVariable(env: ExpressionTypeEnvironment, exp: AccessVariableExpression): ExpressionTypeEnvironment {
        const vinfo = env.lookupLocalVar(exp.name);

        if(vinfo !== null) {
            this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, `${exp.name} may not have been assigned a value`);
            return env.setResultExpressionInfo(new TIRAccessVariableExpression(exp.sinfo, exp.name, this.toTIRTypeKey(vinfo.declaredType)), vinfo.declaredType);
        }
        else {
            let cvinfo = env.lookupCapturedVar(exp.name);
            this.raiseErrorIf(exp.sinfo, cvinfo === null, `${exp.name} is not defined`);

            return env.setResultExpressionInfo(new TIRAccessCapturedVariableExpression(exp.sinfo, exp.name, this.toTIRTypeKey((cvinfo as VarInfo).declaredType)), (cvinfo as VarInfo).declaredType);
        }
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
                return env.setResultExpressionInfo(econs, roftype);
            }
            else {
                const econs = new TIRConstructorPrimaryCheckExpression(exp.sinfo, tiroftype, eargs.map((earg) => earg.expressionResult));
                return env.setResultExpressionInfo(econs, roftype);
            }
        }
        else if(oftype instanceof ResolvedTypedeclEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);

            this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, `${oftype.typeID} constructor expects a single arg`);
            const cexp = this.checkExpression(env, exp.args[0], ResolvedType.createSingle(oftype.valuetype));
            const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, ResolvedType.createSingle(oftype.valuetype));

            if (!this.typedeclTypeConstructorFromValueHasInvariants(roftype, oftype.object)) {
                const nexp = new TIRTypedeclDirectExpression(exp.sinfo, this.toTIRTypeKey(roftype), ecast.expressionResult);
                return env.setResultExpressionInfo(nexp, roftype);
            }
            else {
                const nexp = new TIRTypedeclConstructorExpression(exp.sinfo, this.toTIRTypeKey(roftype), ecast.expressionResult);
                return env.setResultExpressionInfo(nexp, roftype);
            }
        }
        else if(oftype instanceof ResolvedConstructableEntityAtomType) {
            const roftype = ResolvedType.createSingle(oftype);
            const tiroftype = this.toTIRTypeKey(roftype);

            if(oftype instanceof ResolvedOkEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Result<T, E>::Ok constructor expects a single arg of type T");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeT);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeT);

                return env.setResultExpressionInfo(new TIRResultOkConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedErrEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Result<T, E>::Ok constructor expects a single arg of type E");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeE);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeE);

                return env.setResultExpressionInfo(new TIRResultErrConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedSomethingEntityAtomType) {
                this.raiseErrorIf(exp.sinfo, exp.args.length !== 1, "Something<T> constructor expects a single arg of type T");
                const cexp = this.checkExpression(env, exp.args[0], oftype.typeT);
                const ecast = this.emitCoerceIfNeeded(cexp, exp.sinfo, oftype.typeT);

                return env.setResultExpressionInfo(new TIRSomethingConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            }
            else if(oftype instanceof ResolvedMapEntryEntityAtomType) {
                const tirktype = this.toTIRTypeKey(oftype.typeK);
                const tirvtype = this.toTIRTypeKey(oftype.typeV);

                this.raiseErrorIf(exp.sinfo, exp.args.length !== 2, "MapEntry<K, V> constructor expects two args of type K, V");
                const kexp = this.checkExpression(env, exp.args[0], oftype.typeK);
                const vexp = this.checkExpression(env, exp.args[1], oftype.typeV);

                const kcast = this.emitCoerceIfNeeded(kexp, exp.args[0].sinfo, oftype.typeK);
                const vcast = this.emitCoerceIfNeeded(vexp, exp.args[1].sinfo, oftype.typeV);

                return env.setResultExpressionInfo(new TIRMapEntryConstructorExpression(exp.sinfo, kcast.expressionResult, vcast.expressionResult, tirktype, tirvtype, tiroftype), ResolvedType.createSingle(oftype));
            }
            else {
                this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${oftype.typeID}`);
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
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

                return env.setResultExpressionInfo(new TIRConstructorListExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
            }
            else if(oftype instanceof ResolvedStackEntityAtomType) {
                this.raiseError(exp.sinfo, "Stack<T> not fully supported yet");
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedQueueEntityAtomType) {
                this.raiseError(exp.sinfo, "Queue<T> not fully supported yet");
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedSetEntityAtomType) {
                this.raiseError(exp.sinfo, "Set<T> not fully supported yet");
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
            else if(oftype instanceof ResolvedMapEntityAtomType) {
                const metype = this.normalizeTypeOnly(new NominalTypeSignature(exp.sinfo, "Core", ["MapEntry"], [new TemplateTypeSignature(exp.sinfo, "K"), new TemplateTypeSignature(exp.sinfo, "V")]), TemplateBindScope.createDoubleBindScope("K", oftype.typeK, "V", oftype.typeV));
                
                const eargs = exp.args.map((arg) => {
                    const texp = this.checkExpression(env, arg, metype);
                    return this.emitCoerceIfNeeded(texp, exp.sinfo, metype);
                });

                return env.setResultExpressionInfo(new TIRConstructorMapExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
            }
            else {
                this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${oftype.typeID}`);
                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tiroftype), roftype);
            }
        }
        else {
            this.raiseError(exp.sinfo, `Cannot use explicit constructor on type of ${exp.ctype.getDiagnosticName()}`);
            return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, "None"), ResolvedType.createInvalid());
        }
    }

    private checkTupleConstructor(env: ExpressionTypeEnvironment, exp: ConstructorTupleExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedTupleAtomType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedTupleAtomType && desiredtype.options[0].types.length === exp.args.length) {
            itype = desiredtype.options[0]
        }

        if(itype === undefined) {
            const eargs = exp.args.map((arg) => this.checkExpression(env, arg, undefined));

            const roftype = ResolvedType.createSingle(ResolvedTupleAtomType.create(eargs.map((ee) => ee.trepr)));
            const tiroftype = this.toTIRTypeKey(roftype);

            return env.setResultExpressionInfo(new TIRConstructorTupleExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
        }
        else {
            const topts = itype.types;
            const eargs = exp.args.map((arg, i) => {
                const texp = this.checkExpression(env, arg, topts[i]);
                return this.emitCoerceIfNeeded(texp, exp.sinfo, topts[i]);
            });
        
            const roftype = ResolvedType.createSingle(itype);
            const tiroftype = this.toTIRTypeKey(roftype);

            return env.setResultExpressionInfo(new TIRConstructorTupleExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
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
                return {pname: ee.pname, ptype: ee.penv.trepr};
            })));
            const tiroftype = this.toTIRTypeKey(roftype);

            return env.setResultExpressionInfo(new TIRConstructorRecordExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.penv.expressionResult)), roftype);
        }
        else {
            const roftype = ResolvedType.createSingle(itype);
            const tiroftype = this.toTIRTypeKey(roftype);

            for(let i = 0; i < itype.entries.length; ++i) {
                if(itype.entries[i].pname !== exp.args[i].property) {
                    this.raiseError(exp.sinfo, `expected property name ${itype.entries[i].pname} but got ${exp.args[i].property}`);
                    return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, "None"), roftype);
                }
            }

            const topts = itype.entries;
            const eargs = exp.args.map((arg, i) => {
                const texp = this.checkExpression(env, arg.value, topts[i].ptype);
                return this.emitCoerceIfNeeded(texp, exp.sinfo, topts[i].ptype);
            });

            return env.setResultExpressionInfo(new TIRConstructorRecordExpression(exp.sinfo, tiroftype, eargs.map((arg) => arg.expressionResult)), roftype);
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

            const consenv = ecast.setResultExpressionInfo(new TIRSomethingConstructorExpression(exp.sinfo, tiroftype, ecast.expressionResult), roftype);
            if(desiredtype === undefined) {
                return consenv; 
            }
            else {
                return this.emitCoerceIfNeeded(consenv, exp.sinfo, desiredtype);
            }
        }
        else {
            this.raiseErrorIf(exp.sinfo, desiredtype === undefined || (desiredtype.options.length !== 1 || !(desiredtype as ResolvedType).typeID.startsWith("Result<")), "ok/err/result shorthand constructors only valid with Result typed expressions");
            const T = ((desiredtype as ResolvedType).options[0] as ResolvedConceptAtomType).getTBind();
            const E = ((desiredtype as ResolvedType).options[0] as ResolvedConceptAtomType).getEBind();

            if (exp.rop === "ok") {
                const okenv = this.checkExpression(env, exp.arg, T);
                const tcast = this.emitCoerceIfNeeded(okenv, exp.sinfo, T);

                const rokconstype = this.getOkType(T, E);
                const tirokconstype = this.toTIRTypeKey(rokconstype);

                const consenv = tcast.setResultExpressionInfo(new TIRResultOkConstructorExpression(exp.sinfo, tirokconstype, tcast.expressionResult), rokconstype);
                return this.emitCoerceIfNeeded(consenv, exp.sinfo, desiredtype as ResolvedType);
            }
            else if(exp.rop === "err") {
                const errenv = this.checkExpression(env, exp.arg, E);
                const tcast = this.emitCoerceIfNeeded(errenv, exp.sinfo, E);

                const rerrconstype = this.getErrType(T, E);
                const tirerrconstype = this.toTIRTypeKey(rerrconstype);

                const consenv = tcast.setResultExpressionInfo(new TIRResultErrConstructorExpression(exp.sinfo, tirerrconstype, tcast.expressionResult), rerrconstype);
                return this.emitCoerceIfNeeded(consenv, exp.sinfo, desiredtype as ResolvedType);
            }
            else {
                this.raiseError(exp.sinfo, "TODO: result special constructor is not supported yet");
                //TODO: this should best effort (1) convert Result<T, E> into Result<U, V> + coearce T values into Ok<T> and E values into Err<E> Results -- as possible

                return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, this.toTIRTypeKey(this.getSpecialNoneType())), ResolvedType.createInvalid());
            }
        }
    }

    private checkPCodeInvokeExpression(env: ExpressionTypeEnvironment, exp: PCodeInvokeExpression): ExpressionTypeEnvironment {
        const pco = env.argpcodes.get(exp.pcode);
        if (pco !== undefined) {
            const pcload = new TIRAccessVariableExpression(exp.sinfo, exp.pcode, pco.pcode.codekey);
            const args = exp.args.map((arg, ii) => this.emitCoerceIfNeeded(this.checkExpression(env, arg, pco.ftype.params[ii].type as ResolvedType), arg.sinfo, pco.ftype.params[ii].type as ResolvedType).expressionResult);
            const pci = new TIRCodePackInvokeExpression(exp.sinfo, this.toTIRTypeKey(pco.ftype.resultType), pco.pcode, [pcload, ...args]);

            return env.setResultExpressionInfo(pci, pco.ftype.resultType);
        }
        else {
            const pcotry = env.capturedpcodes.get(exp.pcode);
            this.raiseErrorIf(exp.sinfo, pcotry === undefined, `missing binding for lambda invoke -- ${exp.pcode}`);
            const pco = pcotry as { pcode: TIRCodePack, ftype: ResolvedFunctionType };

            const pcload = new TIRAccessCapturedVariableExpression(exp.sinfo, exp.pcode, pco.pcode.codekey);
            const args = exp.args.map((arg, ii) => this.emitCoerceIfNeeded(this.checkExpression(env, arg, pco.ftype.params[ii].type as ResolvedType), arg.sinfo, pco.ftype.params[ii].type as ResolvedType).expressionResult);
            const pci = new TIRCodePackInvokeExpression(exp.sinfo, this.toTIRTypeKey(pco.ftype.resultType), pco.pcode, [pcload, ...args]);

            return env.setResultExpressionInfo(pci, pco.ftype.resultType);
        }
    }

    private checkCallNamespaceFunctionOrOperatorExpression(env: ExpressionTypeEnvironment, exp: CallNamespaceFunctionOrOperatorExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);

        if(nsdecl.ns === "Core" && exp.name === "s_safeAs") {
            const argenv = this.checkExpression(env, exp.args[0], this.normalizeTypeOnly(exp.terms[0], env.binds));
            const astype = this.normalizeTypeOnly(exp.terms[1], env.binds);

            return this.emitCoerceIfNeeded_NoCheck(argenv, exp.sinfo, astype);
        }
        else {
            if (nsdecl.operators.has(exp.name)) {
                const opsintro = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).find((nso) =>  nso.invoke.attributes.includes("abstract") || nso.invoke.attributes.includes("virtual"));
                const opdecls = (nsdecl.operators.get(exp.name) as NamespaceOperatorDecl[]).filter((nso) => !nso.invoke.attributes.includes("abstract") && !nso.invoke.attributes.includes("virtual"));
                this.raiseErrorIf(exp.sinfo, opsintro !== undefined, "Operator must have exactly one abstract/virtual declaration");
                this.raiseErrorIf(exp.sinfo, opdecls.length === 0, "Operator must have at least one implementation");

                const fkey = TIRIDGenerator.generateInvokeIDForNamespaceOperatorBase(nsdecl.ns, exp.name);
                const rtype = this.normalizeTypeOnly((opsintro as NamespaceOperatorDecl).invoke.resultType, TemplateBindScope.createEmptyBindScope());
                const tirrtype = this.toTIRTypeKey(rtype);

                const [argexps, _] = this.checkArgumentList(exp.sinfo, env, exp.args, (opsintro as NamespaceOperatorDecl).invoke.params, TemplateBindScope.createEmptyBindScope());

                this.m_pendingNamespaceOperators.push({fkey: fkey, decl: opsintro as NamespaceOperatorDecl, impls: opdecls.map((opi, ii) => { return {fkey: TIRIDGenerator.generateInvokeIDForNamespaceOperatorImpl(opi.ns, opi.name, ii), decl: opi}; })});
                const tircall = new TIRCallNamespaceOperatorExpression(exp.sinfo, nsdecl.ns, exp.name, fkey, tirrtype, argexps);
                return env.setResultExpressionInfo(tircall, rtype);
            }
            else {
                this.raiseErrorIf(exp.sinfo, !nsdecl.functions.has(exp.name), `Function named '${exp.name}' is not defined`);
                const fdecl = nsdecl.functions.get(exp.name) as NamespaceFunctionDecl;

                this.raiseErrorIf(exp.sinfo, fdecl.invoke.terms.length !== exp.terms.length, "missing template types");
                let binds = new Map<string, ResolvedType>();
                for(let i = 0; i < fdecl.invoke.terms.length; ++i) {
                    binds.set(fdecl.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], env.binds));
                }
                this.checkTemplateTypesOnInvoke(exp.sinfo, fdecl.invoke.terms, TemplateBindScope.createEmptyBindScope(), binds, fdecl.invoke.termRestrictions);

                const rtype = this.normalizeTypeOnly(fdecl.invoke.resultType, TemplateBindScope.createBaseBindScope(binds));
                const tirrtype = this.toTIRTypeKey(rtype);

                const [argexps, fargs, pcl] = this.checkArgumentList(exp.sinfo, env, exp.args, fdecl.invoke.params, TemplateBindScope.createBaseBindScope(binds));
                const fkey = TIRIDGenerator.generateInvokeIDForNamespaceFunction(nsdecl.ns, exp.name, fdecl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);

                let pcodes = new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>();
                fargs.forEach((ee) => {
                    pcodes.set(ee[0], {iscapture: false, pcode: ee[2], ftype: ee[1]});
                });
                this.m_pendingNamespaceFunctions.push({fkey: fkey, decl: fdecl, binds: binds, pcodes: pcodes});

                const tircall = new TIRCallNamespaceFunctionExpression(exp.sinfo, nsdecl.ns, exp.name, fkey, tirrtype, argexps);
                return env.setResultExpressionInfo(tircall, rtype);
            }
        }
    }

    private checkCallStaticFunctionExpression(env: ExpressionTypeEnvironment, exp: CallStaticFunctionExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.ttype, env.binds);

        const fdecltry = this.resolveMemberFunction(exp.sinfo, oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, (fdecltry === undefined), `Static function/operator not defined for type ${oftype.typeID}`);

        const fdecl = fdecltry as OOMemberLookupInfo<StaticFunctionDecl>;
        this.raiseErrorIf(exp.sinfo, fdecl.decl.invoke.terms.length !== exp.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for(let i = 0; i < fdecl.decl.invoke.terms.length; ++i) {
            binds.set(fdecl.decl.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], env.binds));
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
            this.raiseErrorIf(exp.sinfo, !this.subtypeOf(lhsenv.trepr, ktype), `expected arg of type ${ktype.typeID} but got ${lhsenv.trepr.typeID}`);
            const rhsenv = this.checkExpression(env, exp.args[1], ktype);
            this.raiseErrorIf(exp.sinfo, !this.subtypeOf(rhsenv.trepr, ktype), `expected arg of type ${ktype.typeID} but got ${rhsenv.trepr.typeID}`);

            const tlhs = this.emitCoerceIfNeeded_NoCheck(lhsenv, exp.sinfo, ktype);
            const trhs = this.emitCoerceIfNeeded_NoCheck(rhsenv, exp.sinfo, ktype);

            if (exp.name === "equal") {
                if(ResolvedType.isUniqueType(ktype)) {
                    return env.setResultExpressionInfo(new TIRBinKeyEqBothUniqueExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
                else {
                    return env.setResultExpressionInfo(new TIRBinKeyEqGeneralExpression(exp.sinfo, this.toTIRTypeKey(ktype), tlhs.expressionResult, this.toTIRTypeKey(ktype), trhs.expressionResult), this.getSpecialBoolType());
                }
            }
            else {
                if(ResolvedType.isUniqueType(ktype)) {
                    return env.setResultExpressionInfo(new TIRBinKeyUniqueLessExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
                else {
                    return env.setResultExpressionInfo(new TIRBinKeyGeneralLessExpression(exp.sinfo, tlhs.expressionResult, trhs.expressionResult, this.toTIRTypeKey(ktype)), this.getSpecialBoolType());
                }
            }
        }
        else if ((oftype.typeID === "String" || oftype.typeID === "ASCIIString") && exp.name === "interpolate") {
            this.raiseError(exp.sinfo, "interpolate is not implemented yet");
            return env.setResultExpressionInfo(new TIRInvalidExpression(exp.sinfo, tirrtype), rtype);
        }
        else {
            const [argexps, fargs, pcl] = this.checkArgumentList(exp.sinfo, env, exp.args, fdecl.decl.invoke.params, fdeclscope);

            if (fdecl.decl.invoke.body !== undefined && fdecl.decl.invoke.body.body === "special_inject") {
                return env.setResultExpressionInfo(new TIRInjectExpression(exp.sinfo, argexps[0], tirrtype), rtype);
            }
            else {
                const fkey = TIRIDGenerator.generateInvokeForMemberFunction(this.toTIRTypeKey(fdecl.ttype), exp.name, fdecl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
            
                let pcodes = new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>();
                fargs.forEach((ee) => {
                    pcodes.set(ee[0], {iscapture: false, pcode: ee[2], ftype: ee[1]});
                });
                this.m_pendingFunctionMemberDecls.push({fkey: fkey, decl: fdecl, binds: binds, pcodes: pcodes});

                const tircall = new TIRCallStaticFunctionExpression(exp.sinfo, this.toTIRTypeKey(fdecl.ttype), exp.name, fkey, tirrtype, argexps);
                return env.setResultExpressionInfo(tircall, rtype);
            }
        }
    }

    private checkLogicActionAndExpression(env: ExpressionTypeEnvironment, exp: LogicActionAndExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, exp.args.length === 0, "expected at least 1 argument");
        this.raiseErrorIf(exp.sinfo, exp.args.length < 2, "should test single value directly");

        const bargs = exp.args.map((arg) => this.emitCoerceIfNeeded(this.checkExpression(env, arg, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType()));
        
        return env.setResultExpressionInfo(new TIRLogicActionAndExpression(exp.sinfo, bargs.map((ee) => ee.expressionResult)), this.getSpecialBoolType());
    }

    private checkLogicActionOrExpression(env: ExpressionTypeEnvironment, exp: LogicActionOrExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, exp.args.length === 0, "expected at least 1 argument");
        this.raiseErrorIf(exp.sinfo, exp.args.length < 2, "should test single value directly");
        
        const bargs = exp.args.map((arg) => this.emitCoerceIfNeeded(this.checkExpression(env, arg, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType()));
    
        return env.setResultExpressionInfo(new TIRLogicActionOrExpression(exp.sinfo, bargs.map((ee) => ee.expressionResult)), this.getSpecialBoolType());
    }

    private checkAccessFromIndex(env: ExpressionTypeEnvironment, op: PostfixAccessFromIndex): ExpressionTypeEnvironment {
        this.raiseErrorIf(op.sinfo, env.trepr.options.some((atom) => !(atom instanceof ResolvedTupleAtomType)), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");
        this.raiseErrorIf(op.sinfo, env.trepr.options.some((atom) => (atom as ResolvedTupleAtomType).types.length <= op.index), "Index may not be defined for tuple");

        this.raiseErrorIf(op.sinfo, env.trepr.options.length !== 1, "only a single tuple is permitted -- todo: later want to generalize this")
        const tiroftype = this.toTIRTypeKey(env.trepr);

        const idxtype = (env.trepr.options[0] as ResolvedTupleAtomType).types[op.index];
        const tiridxtype = this.toTIRTypeKey(idxtype);

        return env.setResultExpressionInfo(new TIRLoadIndexExpression(op.sinfo, env.expressionResult, tiroftype, op.index, tiridxtype), idxtype);
    }

    private checkAccessFromName(env: ExpressionTypeEnvironment, op: PostfixAccessFromName): ExpressionTypeEnvironment {
        const isrecord = env.trepr.options.every((atom) => atom instanceof ResolvedRecordAtomType);
        const isobj = env.trepr.options.every((atom) => atom instanceof ResolvedEntityAtomType || atom instanceof ResolvedConceptAtomType);

        this.raiseErrorIf(op.sinfo, !isrecord && !isobj, `Cannot load the named location ${op.name} from type ${env.trepr.typeID}`);
        const tiroftype = this.toTIRTypeKey(env.trepr);

        if (isrecord) {
            this.raiseErrorIf(op.sinfo, env.trepr.options.some((atom) => (atom as ResolvedRecordAtomType).entries.find((entry) => entry.pname === op.name) === undefined), `Property "${op.name}" not be defined for record`);

            const rtype = ((env.trepr.options[0] as ResolvedRecordAtomType).entries.find((entry) => entry.pname === op.name) as {pname: string, ptype: ResolvedType}).ptype;
            const tirrtype = this.toTIRTypeKey(rtype);

            this.raiseErrorIf(op.sinfo, env.trepr.options.length === 0, "only non-virtual property loads are supported for now");
            return env.setResultExpressionInfo(new TIRLoadPropertyExpression(op.sinfo, env.expressionResult, tiroftype, op.name, tirrtype), rtype);
        }
        else {
            const fftry = this.resolveMemberField(op.sinfo, env.trepr, op.name);
            this.raiseErrorIf(op.sinfo, fftry === undefined, `Could not resolve field "${op.name}" on type ${env.trepr.typeID}`);
            const ff = fftry as OOMemberLookupInfo<MemberFieldDecl>;

            const fftype = this.normalizeTypeOnly(ff.decl.declaredType, TemplateBindScope.createBaseBindScope(ff.oobinds));
            const tirfftype = this.toTIRTypeKey(fftype);

            const fkey = TIRIDGenerator.generateMemberFieldID(this.toTIRTypeKey(ff.ttype), op.name);

            if(ff.ootype instanceof EntityTypeDecl) {
                return env.setResultExpressionInfo(new TIRLoadFieldExpression(op.sinfo, tiroftype, env.expressionResult, fkey, tirfftype), fftype);
            }
            else {
                return env.setResultExpressionInfo(new TIRLoadFieldVirtualExpression(op.sinfo, tirfftype, env.expressionResult, fkey, tirfftype), fftype);
            }
        }
    }

    private checkPostfixIs(env: ExpressionTypeEnvironment, op: PostfixIsTest): ExpressionTypeEnvironment {
        const isr = this.processITestAsTestOp(op.sinfo, env.trepr, env.trepr, env.expressionResult, op.ttest, env.binds);
        this.raiseErrorIf(op.sinfo, isr.falseflow === undefined, `test always evaluates to true`);
        this.raiseErrorIf(op.sinfo, !isr.hastrueflow, `test always evaluates to false`);

        return env.setResultExpressionInfo(isr.testexp, this.getSpecialBoolType());
    }

    private checkPostfixAs(env: ExpressionTypeEnvironment, op: PostfixAsConvert): ExpressionTypeEnvironment {
        const isr = this.processITestAsTestOp(op.sinfo, env.trepr, env.trepr, env.expressionResult, op.ttest, env.binds);
        this.raiseErrorIf(op.sinfo, !isr.hastrueflow, `conversion always fails`);

        const csr = this.processITestAsConvertOp(op.sinfo, env.trepr, env.trepr, env.expressionResult, op.ttest, env.binds, false);
        return env.setResultExpressionInfo(csr.asexp as TIRExpression, csr.trueflow as ResolvedType);
    }

    private checkInvoke(env: ExpressionTypeEnvironment, op: PostfixInvoke, refvar: string | undefined): ExpressionTypeEnvironment {
        const resolvefrom = op.specificResolve !== undefined ? this.normalizeTypeOnly(op.specificResolve, env.binds) : env.trepr;
        const mresolvetry = this.resolveMemberMethod(op.sinfo, resolvefrom, op.name);

        this.raiseErrorIf(op.sinfo, op.isRefThis && refvar === undefined, "Cannot call a ref function in this expression position (top-level only)");

        this.raiseErrorIf(op.sinfo, mresolvetry === undefined, `Could not resolve method name "${op.name}" from type ${resolvefrom.typeID}`);
        const mresolve = mresolvetry as OOMemberResolution<MemberMethodDecl>;

        this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.terms.length !== op.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for (let i = 0; i < mresolve.decl.decl.invoke.terms.length; ++i) {
            binds.set(mresolve.decl.decl.invoke.terms[i].name, this.normalizeTypeOnly(op.terms[i], env.binds));
        }
        this.checkTemplateTypesOnInvoke(op.sinfo, mresolve.decl.decl.invoke.terms, TemplateBindScope.createBaseBindScope(mresolve.decl.oobinds), binds, mresolve.decl.decl.invoke.termRestrictions);

        const fdeclscope = TemplateBindScope.createBaseBindScope(mresolve.decl.oobinds).pushScope(binds);
        const rtype = this.normalizeTypeOnly(mresolve.decl.decl.invoke.resultType, fdeclscope);
        const tirrtype = this.toTIRTypeKey(rtype);

        const tirdecltype = this.toTIRTypeKey(mresolve.decl.ttype);

        const [argexps, fargs, pcl] = this.checkArgumentList(op.sinfo, env.createFreshEnvExpressionFrom(), op.args, mresolve.decl.decl.invoke.params, fdeclscope);

        let pcodes = new Map<string, { iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType }>();
        fargs.forEach((ee) => {
                pcodes.set(ee[0], { iscapture: false, pcode: ee[2], ftype: ee[1]});
        });

        if((!mresolve.decl.decl.attributes.includes("abstract") && !mresolve.decl.decl.attributes.includes("virtual"))) {
            this.raiseErrorIf(op.sinfo, mresolve.impl.length !== 1, `Could not resolve implementation for non-virtual method ${op.name} from ${resolvefrom.typeID}`);
            const knownimpl = mresolve.impl[0];

            const tkey = this.toTIRTypeKey(mresolve.impl[0].ttype);
            if (knownimpl.decl.invoke.body !== undefined && (typeof (knownimpl.decl.invoke.body.body) === "string") && (knownimpl.decl.invoke.body.body as string) === "special_extract") {
                this.raiseErrorIf(op.sinfo, op.args.length !== 0, "No arguments permitted on this method");

                return env.setResultExpressionInfo(new TIRExtractExpression(op.sinfo, env.expressionResult, tirrtype), rtype);
            }
            else {
                const knowntype = this.toTIRTypeKey(knownimpl.ttype);
                const knownkey = TIRIDGenerator.generateInvokeForMemberMethod(knowntype, op.name, knownimpl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
                
                const fkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
                this.m_pendingMethodMemberDecls.push({fkey: knownkey, decl: knownimpl, declaredecl: mresolve.decl, binds: binds, pcodes: pcodes}, {fkey: fkey, decl: mresolve.decl, declaredecl: mresolve.decl, binds: binds, pcodes: pcodes});

                const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.impl[0].ttype);
                this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.isThisRef && !(mresolve.impl[0].ootype instanceof EntityTypeDecl), `self call with ref can only be done on non-virtual methods defined on entities but got ${mresolve.impl[0].ttype.typeID}`);

                if (mresolve.decl.decl.invoke.isThisRef) {
                    return env.setResultExpressionInfo(new TIRCallMemberFunctionSelfRefExpression(op.sinfo, this.m_scratchCtr++, tkey, op.name, fkey, tirdecltype, tirrtype, refvar as string, rcvrexp.expressionResult, argexps), rtype);
                }
                else {
                    return env.setResultExpressionInfo(new TIRCallMemberFunctionExpression(op.sinfo, tkey, op.name, fkey, tirdecltype, tirrtype, rcvrexp.expressionResult, argexps), rtype);
                }
            }
        }
        else {
            this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.isThisRef, "cannot use ref on virtual method call -- variance on updated this ref type");
            const tkey = this.toTIRTypeKey(mresolve.decl.ttype);
            const declkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
            this.m_pendingMethodMemberDecls.push({fkey: declkey, decl: mresolve.decl, declaredecl: mresolve.decl, binds: binds, pcodes: pcodes});

            if(resolvefrom.options.length === 1 && ResolvedType.isUniqueType(resolvefrom.options[0])) {
                const inferfimpltype = this.toTIRTypeKey(mresolve.impl[0].ttype);
                const inferfkey = TIRIDGenerator.generateInvokeForMemberMethod(inferfimpltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
                this.m_pendingMethodMemberDecls.push({fkey: inferfkey, decl: mresolve.impl[0], declaredecl: mresolve.decl, binds: binds, pcodes: pcodes});

                const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.impl[0].ttype);
                return env.setResultExpressionInfo(new TIRCallMemberFunctionExpression(op.sinfo, inferfimpltype, op.name, inferfkey, inferfimpltype, tirrtype, rcvrexp.expressionResult, argexps), rtype);
            }
            else {
                const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.decl.ttype);
                return env.setResultExpressionInfo(new TIRCallMemberFunctionDynamicExpression(op.sinfo, tkey, op.name, declkey, tirdecltype, tirrtype, rcvrexp.expressionResult, argexps), rtype);
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
                case PostfixOpTag.PostfixIsTest: {
                    cenv = this.checkPostfixIs(cenv, exp.ops[i] as PostfixIsTest);
                    break;
                }
                case PostfixOpTag.PostfixAsConvert: {
                    cenv = this.checkPostfixAs(cenv, exp.ops[i] as PostfixAsConvert);
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

        return benv.setResultExpressionInfo(new TIRPrefixNotExpression(exp.sinfo, benv.expressionResult), this.getSpecialBoolType());
    }

    private checkPrefixNegateOpExpression(env: ExpressionTypeEnvironment, exp: PrefixNegateOp): ExpressionTypeEnvironment {
        const nenv = this.checkExpression(env, exp.exp, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(nenv.trepr.options), `expected a numeric type but got ${nenv.trepr.typeID}`);

        const ntype = ResolvedType.getNumericBaseRepresentation(nenv.trepr.options);
        this.raiseErrorIf(exp.sinfo, ntype.typeID === "Nat" || ntype.typeID === "BigNat", `cannot negage unsigned type ${nenv.trepr.typeID}`);
        
        return nenv.setResultExpressionInfo(new TIRPrefixNegateExpression(exp.sinfo, nenv.expressionResult, this.toTIRTypeKey(nenv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(ntype))), nenv.trepr);
    }

    private checkBinAddExpression(env: ExpressionTypeEnvironment, exp: BinAddExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.typeID !== renv.trepr.typeID, `addition is defined on numeric values of same type but got -- ${lenv.trepr.typeID} + ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return env.setResultExpressionInfo(new TIRBinAddExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(renv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(nntype))), renv.trepr);
    }

    private checkBinSubExpression(env: ExpressionTypeEnvironment, exp: BinSubExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.typeID !== renv.trepr.typeID, `subtraction is defined on numeric values of same type but got -- ${lenv.trepr.typeID} - ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return env.setResultExpressionInfo(new TIRBinSubExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(renv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(nntype))), renv.trepr);
    }

    private checkBinMultExpression(env: ExpressionTypeEnvironment, exp: BinMultExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        const lnt = ResolvedType.getNumericType(lenv.trepr.options);
        const lnb = ResolvedType.getNumericBaseRepresentation(lenv.trepr.options);

        const rnt = ResolvedType.getNumericType(renv.trepr.options);
        const rnb = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        this.raiseErrorIf(exp.sinfo, lnb.typeID !== rnb.typeID, `underlying numeric types must be compatible but got ${lnb.typeID} * ${rnb.typeID}`);

        if((lnt instanceof ResolvedPrimitiveInternalEntityAtomType) && (rnt instanceof ResolvedPrimitiveInternalEntityAtomType)) {
            return env.setResultExpressionInfo(new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(lenv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
        }
        else if((lnt instanceof ResolvedTypedeclEntityAtomType) && (rnt instanceof ResolvedTypedeclEntityAtomType)) {
            return env.setResultExpressionInfo(new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb)), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnb));
        }
        else {
            this.raiseErrorIf(exp.sinfo, !((lnt instanceof ResolvedTypedeclEntityAtomType) || (rnt instanceof ResolvedTypedeclEntityAtomType)), `multiplication requires at least on unit typed value but got ${lnt.typeID} * ${rnt.typeID}`);

            if(lnt instanceof ResolvedTypedeclEntityAtomType) {
                return env.setResultExpressionInfo(new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(lenv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
            }
            else {
                return env.setResultExpressionInfo(new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(renv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(rnb))), ResolvedType.createSingle(rnt));
            }
        }
    }

    private checkBinDivExpression(env: ExpressionTypeEnvironment, exp: BinDivExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        const lnt = ResolvedType.getNumericType(lenv.trepr.options);
        const lnb = ResolvedType.getNumericBaseRepresentation(lenv.trepr.options);

        const rnt = ResolvedType.getNumericType(renv.trepr.options);
        const rnb = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        this.raiseErrorIf(exp.sinfo, lnb.typeID !== rnb.typeID, `underlying numeric types must be compatible but got ${lnb.typeID} / ${rnb.typeID}`);

        if((lnt instanceof ResolvedPrimitiveInternalEntityAtomType) && (rnt instanceof ResolvedPrimitiveInternalEntityAtomType)) {
            return env.setResultExpressionInfo(new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnt)), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
        }
        else if((lnt instanceof ResolvedTypedeclEntityAtomType) && (rnt instanceof ResolvedTypedeclEntityAtomType)) {
            return env.setResultExpressionInfo(new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb)), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnb));
        }
        else {
            this.raiseErrorIf(exp.sinfo, !(rnt instanceof ResolvedPrimitiveInternalEntityAtomType), `division requires a typed number as numerator and a typed number or a unit type as divisor but got ${lnt.typeID} / ${rnt.typeID}`);

            return env.setResultExpressionInfo(new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnt)), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
        }
    }

    private strongEQ(sinfo: SourceInfo, env: ExpressionTypeEnvironment, lhsarg: Expression, rhsarg: Expression): ExpressionTypeEnvironment {
        const lhsenv = this.checkExpression(env.createFreshEnvExpressionFrom(), lhsarg, undefined);
        const lhstype = lhsenv.trepr;
        const tirlhstype = this.toTIRTypeKey(lhstype);
        
        const rhsenv = this.checkExpression(env.createFreshEnvExpressionFrom(), rhsarg, undefined);
        const rhstype = rhsenv.trepr;
        const tirrhstype = this.toTIRTypeKey(rhstype);
        
        if (!this.subtypeOf(lhstype, rhstype) && !this.subtypeOf(rhstype, lhstype)) {
            this.raiseError(sinfo, `Types ${lhstype.typeID} and ${rhstype.typeID} are not comparable or comparision is always true/false`);
        }

        const action = this.checkValueEq(lhsarg, lhstype, rhsarg, rhstype);
        this.raiseErrorIf(sinfo, action === "err", "Types are not sufficiently overlapping");
        this.raiseErrorIf(sinfo, (action === "truealways" || action === "falsealways"), "equality operation is always true/false");
        
        if (action === "lhsnone") {
            const tr = this.processITestAsTest_None(sinfo, rhsenv.trepr, rhsenv.trepr, rhsenv.expressionResult, false);
            return env.setResultExpressionInfo(tr.testexp, this.getSpecialBoolType());
        }
        else if (action === "rhsnone") {
            const tl = this.processITestAsTest_None(sinfo, lhsenv.trepr, lhsenv.trepr, lhsenv.expressionResult, false);
            return env.setResultExpressionInfo(tl.testexp, this.getSpecialBoolType());
        }
        else if (action === "lhsnothing") {
            const tr = this.processITestAsTest_Nothing(sinfo, rhsenv.trepr, rhsenv.trepr, rhsenv.expressionResult, false);
            return env.setResultExpressionInfo(tr.testexp, this.getSpecialBoolType());
        }
        else if (action === "rhsnothing") {
            const tl = this.processITestAsTest_Nothing(sinfo, lhsenv.trepr, lhsenv.trepr, lhsenv.expressionResult, false);
            return env.setResultExpressionInfo(tl.testexp, this.getSpecialBoolType());
        }
        else {
            if (action === "stdkeywithunique") {
                this.raiseErrorIf(lhsarg.sinfo, !(this.subtypeOf(lhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${lhstype.typeID}`);
                this.raiseErrorIf(rhsarg.sinfo, !(this.subtypeOf(rhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${rhstype.typeID}`);

                const eqop = new TIRBinKeyEqBothUniqueExpression(sinfo, lhsenv.expressionResult, rhsenv.expressionResult, tirlhstype);
                return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
            }
            else if (action === "lhssomekeywithunique") {
                this.raiseErrorIf(lhsarg.sinfo, !(this.subtypeOf(lhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${lhstype.typeID}`);

                const eqop = new TIRBinKeyEqOneUniqueExpression(sinfo, tirlhstype, lhsenv.expressionResult, this.toTIRTypeKey(rhsenv.trepr), rhsenv.expressionResult);
                return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
            }
            else if (action === "rhssomekeywithunique") {
                this.raiseErrorIf(rhsarg.sinfo, !(this.subtypeOf(rhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${rhstype.typeID}`);

                const eqop = new TIRBinKeyEqOneUniqueExpression(sinfo, tirrhstype, rhsenv.expressionResult, this.toTIRTypeKey(lhsenv.trepr), lhsenv.expressionResult);
                return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
            }
            else {
                const eqop = new TIRBinKeyEqGeneralExpression(sinfo, this.toTIRTypeKey(lhsenv.trepr), lhsenv.expressionResult, this.toTIRTypeKey(rhsenv.trepr), rhsenv.expressionResult);

                if (action === "lhssomekey") {
                    this.raiseErrorIf(lhsarg.sinfo, !(this.subtypeOf(lhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${lhstype.typeID}`);

                    return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
                }
                else if (action === "rhssomekey") {
                    this.raiseErrorIf(rhsarg.sinfo, !(this.subtypeOf(rhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${rhstype.typeID}`);

                    return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
                }
                else {
                    this.raiseErrorIf(lhsarg.sinfo, !(this.subtypeOf(lhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${lhstype.typeID}`);
                    this.raiseErrorIf(rhsarg.sinfo, !(this.subtypeOf(rhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${rhstype.typeID}`);

                    return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
                }
            }
        }
    }

    private strongNEQ(sinfo: SourceInfo, env: ExpressionTypeEnvironment, lhsarg: Expression, rhsarg: Expression): ExpressionTypeEnvironment {
        const lhsenv = this.checkExpression(env.createFreshEnvExpressionFrom(), lhsarg, undefined);
        const lhstype = lhsenv.trepr;
        const tirlhstype = this.toTIRTypeKey(lhstype);
        
        const rhsenv = this.checkExpression(env.createFreshEnvExpressionFrom(), rhsarg, undefined);
        const rhstype = rhsenv.trepr;
        const tirrhstype = this.toTIRTypeKey(rhstype);
        
        if (!this.subtypeOf(lhstype, rhstype) && !this.subtypeOf(rhstype, lhstype)) {
            this.raiseError(sinfo, `Types ${lhstype.typeID} and ${rhstype.typeID} are not comparable or comparision is always true/false`);
        }

        const action = this.checkValueEq(lhsarg, lhstype, rhsarg, rhstype);
        this.raiseErrorIf(sinfo, action === "err", "Types are not sufficiently overlapping");
        this.raiseErrorIf(sinfo, (action === "truealways" || action === "falsealways"), "equality operation is always true/false");

        if (action === "lhsnone") {
            const tr = this.processITestAsTest_None(sinfo, rhsenv.trepr, rhsenv.trepr, rhsenv.expressionResult, true);
            return env.setResultExpressionInfo(tr.testexp, this.getSpecialBoolType());
        }
        else if (action === "rhsnone") {
            const tl = this.processITestAsTest_None(sinfo, lhsenv.trepr, lhsenv.trepr, lhsenv.expressionResult, true);
            return env.setResultExpressionInfo(tl.testexp, this.getSpecialBoolType());
        }
        else if (action === "lhsnothing") {
            const tr = this.processITestAsTest_Nothing(sinfo, rhsenv.trepr, rhsenv.trepr, rhsenv.expressionResult, true);
            return env.setResultExpressionInfo(tr.testexp, this.getSpecialBoolType());
        }
        else if (action === "rhsnothing") {
            const tl = this.processITestAsTest_Nothing(sinfo, lhsenv.trepr, lhsenv.trepr, lhsenv.expressionResult, true);
            return env.setResultExpressionInfo(tl.testexp, this.getSpecialBoolType());
        }
        else {
            if (action === "stdkeywithunique") {
                this.raiseErrorIf(lhsarg.sinfo, !(this.subtypeOf(lhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${lhstype.typeID}`);
                this.raiseErrorIf(rhsarg.sinfo, !(this.subtypeOf(rhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${rhstype.typeID}`);

                const eqop = new TIRBinKeyNeqBothUniqueExpression(sinfo, lhsenv.expressionResult, rhsenv.expressionResult, tirlhstype);
                return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
            }
            else if (action === "lhssomekeywithunique") {
                this.raiseErrorIf(lhsarg.sinfo, !(this.subtypeOf(lhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${lhstype.typeID}`);

                const eqop = new TIRBinKeyNeqOneUniqueExpression(sinfo, tirlhstype, lhsenv.expressionResult, this.toTIRTypeKey(rhsenv.trepr), rhsenv.expressionResult);
                return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
            }
            else if (action === "rhssomekeywithunique") {
                this.raiseErrorIf(rhsarg.sinfo, !(this.subtypeOf(rhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${rhstype.typeID}`);

                const eqop = new TIRBinKeyNeqOneUniqueExpression(sinfo, tirrhstype, rhsenv.expressionResult, this.toTIRTypeKey(lhsenv.trepr), lhsenv.expressionResult);
                return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
            }
            else {
                const eqop = new TIRBinKeyNeqGeneralExpression(sinfo, this.toTIRTypeKey(lhsenv.trepr), lhsenv.expressionResult, this.toTIRTypeKey(rhsenv.trepr), rhsenv.expressionResult);

                if (action === "lhssomekey") {
                    this.raiseErrorIf(lhsarg.sinfo, !(this.subtypeOf(lhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${lhstype.typeID}`);

                    return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
                }
                else if (action === "rhssomekey") {
                    this.raiseErrorIf(rhsarg.sinfo, !(this.subtypeOf(rhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${rhstype.typeID}`);

                    return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
                }
                else {
                    this.raiseErrorIf(lhsarg.sinfo, !(this.subtypeOf(lhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(lhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${lhstype.typeID}`);
                    this.raiseErrorIf(rhsarg.sinfo, !(this.subtypeOf(rhstype, this.getSpecialKeyTypeConceptType()) && ResolvedType.isGroundedType(rhstype.options)), `left hand side of compare expression -- expected a grounded KeyType but got ${rhstype.typeID}`);

                    return env.setResultExpressionInfo(eqop, this.getSpecialBoolType());
                }
            }
        }
    }

    private checkNumericEqExpression(env: ExpressionTypeEnvironment, exp: NumericEqExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, !lenv.trepr.isSameType(renv.trepr), `equality is defined on numeric values of same type but got -- ${lenv.trepr.typeID} == ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return env.setResultExpressionInfo(new TIRNumericEqExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericNeqExpression(env: ExpressionTypeEnvironment, exp: NumericNeqExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, !lenv.trepr.isSameType(renv.trepr), `equality is defined on numeric values of same type but got -- ${lenv.trepr.typeID} != ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return env.setResultExpressionInfo(new TIRNumericNeqExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericLessExpression(env: ExpressionTypeEnvironment, exp: NumericLessExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, !lenv.trepr.isSameType(renv.trepr), `order is defined on numeric values of same type but got -- ${lenv.trepr.typeID} < ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return env.setResultExpressionInfo(new TIRNumericLessExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericLessEqExpression(env: ExpressionTypeEnvironment, exp: NumericLessEqExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, !lenv.trepr.isSameType(renv.trepr), `order is defined on numeric values of same type but got -- ${lenv.trepr.typeID} <= ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return env.setResultExpressionInfo(new TIRNumericLessEqExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericGreaterExpression(env: ExpressionTypeEnvironment, exp: NumericGreaterExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, !lenv.trepr.isSameType(renv.trepr), `order is defined on numeric values of same type but got -- ${lenv.trepr.typeID} > ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return env.setResultExpressionInfo(new TIRNumericGreaterExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkNumericGreaterEqExpression(env: ExpressionTypeEnvironment, exp: NumericGreaterEqExpression): ExpressionTypeEnvironment {
        const lenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, !lenv.trepr.isSameType(renv.trepr), `order is defined on numeric values of same type but got -- ${lenv.trepr.typeID} >= ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return env.setResultExpressionInfo(new TIRNumericGreaterEqExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(nntype))), this.getSpecialBoolType());
    }

    private checkBinLogicAnd(env: ExpressionTypeEnvironment, exp: BinLogicAndxpression): ExpressionTypeEnvironment {
        const lhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        const rhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        
        const andexp = new TIRBinLogicAndExpression(exp.sinfo, lhs.expressionResult, rhs.expressionResult);
        return env.setResultExpressionInfo(andexp, this.getSpecialBoolType());
    }

    private checkBinLogicOr(env: ExpressionTypeEnvironment, exp: BinLogicOrExpression): ExpressionTypeEnvironment {
        const lhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        const rhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        
        const orexp = new TIRBinLogicOrExpression(exp.sinfo, lhs.expressionResult, rhs.expressionResult);
        return env.setResultExpressionInfo(orexp, this.getSpecialBoolType());
    }

    private checkBinLogicImplies(env: ExpressionTypeEnvironment, exp: BinLogicImpliesExpression): ExpressionTypeEnvironment {
        const lhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());
        const rhs = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, this.getSpecialBoolType()), exp.sinfo, this.getSpecialBoolType());

        const impliesexp = new TIRBinLogicImpliesExpression(exp.sinfo, lhs.expressionResult, rhs.expressionResult);
        return env.setResultExpressionInfo(impliesexp, this.getSpecialBoolType());
    }

    private checkMapEntryConstructorExpression(env: ExpressionTypeEnvironment, exp: MapEntryConstructorExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let itype: ResolvedMapEntityAtomType | undefined = undefined;
        if(desiredtype !== undefined && desiredtype.options.length === 1 && desiredtype.options[0] instanceof ResolvedMapEntryEntityAtomType) {
            itype = desiredtype.options[0]
        }

        const kenv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.kexp, itype !== undefined ? itype.typeK : undefined);
        const venv = this.checkExpression(env.createFreshEnvExpressionFrom(), exp.vexp, itype !== undefined ? itype.typeV : undefined);

        this.raiseErrorIf(exp.kexp.sinfo, !this.subtypeOf(kenv.trepr, this.getSpecialKeyTypeConceptType()) || !ResolvedType.isGroundedType(kenv.trepr.options), "Key must be a grounded KeyType value");
        if(itype !== undefined) {
            const ktype = this.toTIRTypeKey(itype.typeK);
            const kexp = this.emitCoerceIfNeeded(kenv, exp.kexp.sinfo, itype.typeK);

            const vtype = this.toTIRTypeKey(itype.typeV);
            const vexp = this.emitCoerceIfNeeded(venv, exp.vexp.sinfo, itype.typeV);

            const medecl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("MapEntry") as EntityTypeDecl; 
            const metype = ResolvedType.createSingle(ResolvedMapEntryEntityAtomType.create(medecl, itype.typeK, itype.typeV));
            const oftype = this.toTIRTypeKey(metype);

            return env.setResultExpressionInfo(new TIRMapEntryConstructorExpression(exp.sinfo, kexp.expressionResult, vexp.expressionResult, ktype, vtype, oftype), metype);
        }
        else {
            const ktype = this.toTIRTypeKey(kenv.trepr);
            const kexp = kenv.expressionResult;

            const vtype = this.toTIRTypeKey(venv.trepr);
            const vexp = venv.expressionResult;

            const medecl = this.m_assembly.tryGetObjectTypeForFullyResolvedName("MapEntry") as EntityTypeDecl; 
            const metype = ResolvedType.createSingle(ResolvedMapEntryEntityAtomType.create(medecl, kenv.trepr, venv.trepr));
            const oftype = this.toTIRTypeKey(metype);

            return env.setResultExpressionInfo(new TIRMapEntryConstructorExpression(exp.sinfo, kexp, vexp, ktype, vtype, oftype), metype);
        }
    }

    private checkIfExpression(env: ExpressionTypeEnvironment, exp: IfExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        let results: {test: ExpressionTypeEnvironment, value: ExpressionTypeEnvironment, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined}[] = [];

        let testflowtypes = new Map<string, ResolvedType>();
        let elsebind: [TIRExpression, ResolvedType] | undefined | null = undefined;

        for (let i = 0; i < exp.condflow.length; ++i) {
            if(exp.condflow[i].cond.itestopt === undefined) {
                const tenv = this.emitCoerceIfNeeded(this.checkExpression(env, exp.condflow[i].cond.exp, this.getSpecialBoolType()), exp.condflow[i].cond.exp.sinfo, this.getSpecialBoolType());
                elsebind = null;

                this.raiseErrorIf(exp.condflow[i].value.sinfo, exp.condflow[i].binderinfo !== undefined, "Binder doesn't make sense here -- will be bound to true");
                
                const resenv = this.checkExpression(env, exp.condflow[i].value, desiredtype);
                results.push({ test: tenv, value: resenv, binderinfo: undefined });
            }
            else {
                const eenv = this.checkExpression(env, exp.condflow[i].cond.exp, undefined);
                const eenvflowtype = testflowtypes.get(eenv.expressionResult.expstr) || eenv.trepr;

                if(elsebind === null) {
                    elsebind = null;
                }
                else if(elsebind === undefined) {
                    elsebind = [eenv.expressionResult, eenv.trepr];
                }
                else {
                    elsebind = (elsebind[0].expstr === eenv.expressionResult.expstr) ? elsebind : null;
                }

                if(exp.condflow[i].binderinfo === undefined) {
                    const resenv = this.checkExpression(env, exp.condflow[i].value, desiredtype);
                    const testinfo = this.processITestAsTestOp(exp.condflow[i].cond.exp.sinfo, eenv.trepr, eenvflowtype, eenv.expressionResult, exp.condflow[i].cond.itestopt as ITest, eenv.binds);
                    this.raiseErrorIf(exp.condflow[i].cond.exp.sinfo, testinfo.falseflow === undefined, `test always evaluates to true`);
                    this.raiseErrorIf(exp.condflow[i].cond.exp.sinfo, !testinfo.hastrueflow, `test always evaluates to false`);

                    testflowtypes.set(eenv.expressionResult.expstr, testinfo.falseflow as ResolvedType);

                    results.push({ test: eenv.setResultExpressionInfo(testinfo.testexp, this.getSpecialBoolType()), value: resenv, binderinfo: undefined });
                }
                else {
                    const scratchidx = this.m_scratchCtr++;
                    const testinfo = this.processITestAsTestOp(exp.condflow[i].cond.exp.sinfo, eenv.trepr, eenvflowtype, new TIRAccessScratchSingleValueExpression(exp.condflow[i].cond.exp.sinfo, this.toTIRTypeKey(eenv.trepr), scratchidx), exp.condflow[i].cond.itestopt as ITest, eenv.binds);
                    this.raiseErrorIf(exp.condflow[i].cond.exp.sinfo, testinfo.falseflow === undefined, `test always evaluates to true`);
                    this.raiseErrorIf(exp.condflow[i].cond.exp.sinfo, !testinfo.hastrueflow, `test always evaluates to false`);

                    testflowtypes.set(eenv.expressionResult.expstr, testinfo.falseflow as ResolvedType);

                    const asinfo = this.processITestAsConvertOp(exp.condflow[i].value.sinfo, eenv.trepr, eenvflowtype, new TIRAccessScratchSingleValueExpression(exp.condflow[i].cond.exp.sinfo, this.toTIRTypeKey(eenv.trepr), scratchidx), exp.condflow[i].cond.itestopt as ITest, eenv.binds, true);
                    const bindtype = asinfo.trueflow as ResolvedType;

                    const flowenv = eenv.pushBinderFrame(exp.condflow[i].binderinfo as string, bindtype);
                    const resenv = this.checkExpression(flowenv, exp.condflow[i].value, desiredtype);
                    results.push({ test: eenv.setResultExpressionInfo(testinfo.testexp, this.getSpecialBoolType()), value: resenv, binderinfo: [eenv.expressionResult, scratchidx, asinfo.asexp as TIRExpression, exp.condflow[i].binderinfo as string]});
                }
            }
        }

        if(exp.elseflow.binderinfo === undefined) {
            const resenv = this.checkExpression(env, exp.elseflow.value, desiredtype);
            results.push({ test: env.setResultExpressionInfo(new TIRLiteralBoolExpression(exp.elseflow.value.sinfo, true), this.getSpecialBoolType()), value: resenv, binderinfo: undefined});
        }
        else {
            this.raiseErrorIf(exp.elseflow.value.sinfo, elsebind === undefined || elsebind === null, "cannot use binder in else unless all previous clauses test same expression and use ITests");

            const scratchidx = this.m_scratchCtr++;
            const [elseexpr, elsetype] = elsebind as [TIRExpression, ResolvedType];
            const bindtype = testflowtypes.get(elseexpr.expstr) as ResolvedType;
            const bindexp = this.emitCoerceIfNeeded_NoCheck(env.setResultExpressionInfo(new TIRAccessScratchSingleValueExpression(exp.elseflow.value.sinfo, this.toTIRTypeKey(elsetype), scratchidx), elsetype), exp.elseflow.value.sinfo, bindtype).expressionResult;
            
            const flowenv = env.pushBinderFrame(exp.elseflow.binderinfo as string, bindtype);
            const resenv = this.checkExpression(flowenv, exp.elseflow.value, desiredtype);

            results.push({ test: env.setResultExpressionInfo(new TIRLiteralBoolExpression(exp.elseflow.value.sinfo, true), this.getSpecialBoolType()), value: resenv, binderinfo: [elseexpr as TIRExpression, scratchidx, bindexp, exp.elseflow.binderinfo as string]});
        }
        const iftype = this.normalizeUnionList([...(desiredtype !== undefined ? [desiredtype] : []), ...results.map((eev) => eev.value.trepr)]);
        
        const ifcl = {test: results[0].test.expressionResult, value: this.emitCoerceIfNeeded(results[0].value, results[0].value.expressionResult.sinfo, iftype).expressionResult, binderinfo: results[0].binderinfo};

        const elifcl = results.slice(1, results.length - 1).map((rr) => {
            return {test: rr.test.expressionResult, value: this.emitCoerceIfNeeded(rr.value, rr.value.expressionResult.sinfo, iftype).expressionResult, binderinfo: rr.binderinfo};
        });
        
        const elsecl = {value: this.emitCoerceIfNeeded(results[results.length - 1].value, results[results.length - 1].value.expressionResult.sinfo, iftype).expressionResult, binderinfo: results[results.length - 1].binderinfo};

        const rexp = new TIRIfExpression(exp.sinfo, this.toTIRTypeKey(iftype), ifcl, elifcl, elsecl);
        return env.setResultExpressionInfo(rexp, iftype);
    }

    private checkSwitchExpression(env: ExpressionTypeEnvironment, exp: SwitchExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const venv = this.checkExpression(env, exp.sval, undefined);
        
        const scratchidx = this.m_scratchCtr++;
        let ctype: ResolvedType = venv.trepr;
        let exhaustive = false;
        let results: {test: TIRExpression | undefined, value: ExpressionTypeEnvironment, binderinfo: [TIRExpression, string] | undefined}[] = [];

        for (let i = 0; i < exp.switchflow.length; ++i) {
            //it is a wildcard match
            if(exp.switchflow[i].condlit === undefined) {
                this.raiseErrorIf(exp.sinfo, i !== exp.switchflow.length - 1, `wildcard should be last option in switch expression but there were ${exp.switchflow.length - (i + 1)} more that are unreachable`);

                let senv = venv;
                let binderinfo: [TIRExpression, string] | undefined = undefined;
                if (exp.switchflow[i].bindername !== undefined) {
                    binderinfo = [this.generateCoerceExpForITestConv(new TIRAccessScratchSingleValueExpression(exp.switchflow[i].value.sinfo, this.toTIRTypeKey(venv.trepr), scratchidx), venv.trepr, exp.switchflow[i].value.sinfo, ctype), exp.switchflow[i].bindername as string];
                    senv = senv.pushBinderFrame(exp.switchflow[i].bindername as string, ctype);
                }
                const trueenv = this.checkExpression(senv, exp.switchflow[i].value, desiredtype);

                results.push({test: undefined, value: trueenv, binderinfo: binderinfo});

                exhaustive = true;
                break;
            }
            else {
                const condsinfo = (exp.switchflow[i].condlit as LiteralExpressionValue).exp.sinfo;

                const test = this.processITestAsTestOp(condsinfo, venv.trepr, ctype, new TIRAccessScratchSingleValueExpression(condsinfo, this.toTIRTypeKey(venv.trepr), scratchidx), new ITestLiteral(false, exp.switchflow[i].condlit as LiteralExpressionValue), venv.binds);
                this.raiseErrorIf(condsinfo, !test.hastrueflow, `test always evaluates to false`);
                this.raiseErrorIf(condsinfo, i !== exp.switchflow.length - 1 && test.falseflow === undefined, "test is always true (and cases below will never be reached)");
                
                const conv = this.processITestAsConvertOp(condsinfo, venv.trepr, ctype, new TIRAccessScratchSingleValueExpression(condsinfo, this.toTIRTypeKey(venv.trepr), scratchidx), new ITestLiteral(false, exp.switchflow[i].condlit as LiteralExpressionValue), venv.binds, true);
                ctype = test.falseflow as ResolvedType;

                let senv = venv;
                let binderinfo: [TIRExpression, string] | undefined = undefined;
                if (exp.switchflow[i].bindername !== undefined) {
                    binderinfo = [conv.asexp as TIRExpression, exp.switchflow[i].bindername as string];
                    senv = senv.pushBinderFrame(exp.switchflow[i].bindername as string, conv.trueflow as ResolvedType);
                }
                const trueenv = this.checkExpression(senv, exp.switchflow[i].value, desiredtype);
                
                results.push({test: test.testexp, value: trueenv, binderinfo: binderinfo});
            }
        }

        const stype = this.normalizeUnionList([...(desiredtype !== undefined ? [desiredtype] : []), ...results.map((eev) => eev.value.trepr)]);
        const clauses = results
            .filter((ffp) => ffp.test !== undefined)
            .map((ffp) => {
                return { match: ffp.test as TIRExpression, value: this.emitCoerceIfNeeded(ffp.value, ffp.value.expressionResult.sinfo, stype).expressionResult, binderinfo: ffp.binderinfo };
            });
        const edefault = results.find((ffp) => ffp.test === undefined) ? {value: this.emitCoerceIfNeeded(results[results.length - 1].value, exp.switchflow[exp.switchflow.length - 1].value.sinfo, stype).expressionResult, binderinfo: results[results.length - 1].binderinfo} : undefined;

        const rexp = new TIRSwitchExpression(exp.sinfo, this.toTIRTypeKey(stype), venv.expressionResult, scratchidx, clauses, edefault, exhaustive || ctype === undefined);
        return env.setResultExpressionInfo(rexp, stype);
    }

    private checkMatchExpression(env: ExpressionTypeEnvironment, exp: MatchExpression, desiredtype: ResolvedType | undefined): ExpressionTypeEnvironment {
        const venv = this.checkExpression(env, exp.sval, undefined);
        
        const scratchidx = this.m_scratchCtr++;
        let ctype: ResolvedType = venv.trepr;
        let exhaustive = false;
        let results: {test: TIRExpression | undefined, value: ExpressionTypeEnvironment, binderinfo: [TIRExpression, string] | undefined}[] = [];

        for (let i = 0; i < exp.matchflow.length; ++i) {
            //it is a wildcard match
            if(exp.matchflow[i].mtype === undefined) {
                this.raiseErrorIf(exp.sinfo, i !== exp.matchflow.length - 1, `wildcard should be last option in switch expression but there were ${exp.matchflow.length - (i + 1)} more that are unreachable`);

                let senv = venv;
                let binderinfo: [TIRExpression, string] | undefined = undefined;
                if (exp.matchflow[i].bindername !== undefined) {
                    binderinfo = [this.generateCoerceExpForITestConv(new TIRAccessScratchSingleValueExpression(exp.matchflow[i].value.sinfo, this.toTIRTypeKey(venv.trepr), scratchidx), venv.trepr, exp.matchflow[i].value.sinfo, ctype), exp.matchflow[i].bindername as string];
                    senv = senv.pushBinderFrame(exp.matchflow[i].bindername as string, ctype);
                }
                const trueenv = this.checkExpression(senv, exp.matchflow[i].value, desiredtype);

                results.push({test: undefined, value: trueenv, binderinfo: binderinfo});

                exhaustive = true;
                break;
            }
            else {
                const condsinfo = (exp.matchflow[i].mtype as TypeSignature).sinfo;

                const test = this.processITestAsTestOp(condsinfo, venv.trepr, ctype, new TIRAccessScratchSingleValueExpression(condsinfo, this.toTIRTypeKey(venv.trepr), scratchidx), new ITestType(false, exp.matchflow[i].mtype as TypeSignature), venv.binds);
                this.raiseErrorIf(condsinfo, !test.hastrueflow, `test always evaluates to false`);
                this.raiseErrorIf(condsinfo, i !== exp.matchflow.length - 1 && test.falseflow === undefined, "test is always true (and cases below will never be reached)");
                
                const conv = this.processITestAsConvertOp(condsinfo, venv.trepr, ctype, new TIRAccessScratchSingleValueExpression(condsinfo, this.toTIRTypeKey(venv.trepr), scratchidx), new ITestType(false, exp.matchflow[i].mtype as TypeSignature), venv.binds, true);
                ctype = test.falseflow as ResolvedType;

                let senv = venv;
                let binderinfo: [TIRExpression, string] | undefined = undefined;
                if (exp.matchflow[i].bindername !== undefined) {
                    binderinfo = [conv.asexp as TIRExpression, exp.matchflow[i].bindername as string];
                    senv = senv.pushBinderFrame(exp.matchflow[i].bindername as string, conv.trueflow as ResolvedType);
                }
                const trueenv = this.checkExpression(senv, exp.matchflow[i].value, desiredtype);
                
                results.push({test: test.testexp, value: trueenv, binderinfo: binderinfo});
            }
        }

        const stype = this.normalizeUnionList([...(desiredtype !== undefined ? [desiredtype] : []), ...results.map((eev) => eev.value.trepr)]);
        const clauses = results
            .filter((ffp) => ffp.test !== undefined)
            .map((ffp) => {
                return { match: ffp.test as TIRExpression, value: this.emitCoerceIfNeeded(ffp.value, ffp.value.expressionResult.sinfo, stype).expressionResult, binderinfo: ffp.binderinfo };
            });
        const edefault = results.find((ffp) => ffp.test === undefined) ? {value: this.emitCoerceIfNeeded(results[results.length - 1].value, exp.matchflow[exp.matchflow.length - 1].value.sinfo, stype).expressionResult, binderinfo: results[results.length - 1].binderinfo} : undefined;

        const rexp = new TIRMatchExpression(exp.sinfo, this.toTIRTypeKey(stype), venv.expressionResult, scratchidx, clauses, edefault, exhaustive || ctype === undefined);
        return env.setResultExpressionInfo(rexp, stype);
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

        const fkey = TIRIDGenerator.generateMemberFieldID(this.toTIRTypeKey(tasktype), exp.sfield);
        return env.setResultExpressionInfo(new TIRTaskSelfFieldExpression(exp.sinfo, this.toTIRTypeKey(tasktype), fkey, exp.sfield, tirfftype), fftype);
    }

    private checkTaskAccessSelfControl(env: ExpressionTypeEnvironment, exp: TaskSelfControlExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        const ffctl = ResolvedType.createSingle(ResolvedRecordAtomType.create(tsk.taskdecl.econtrol.map((ec) => {
            return {
                pname: ec.name,
                ptype: this.normalizeTypeOnly(ec.declaredType, TemplateBindScope.createBaseBindScope(tsk.taskbinds))
            }
        })));

        const tirtask = this.toTIRTypeKey(tasktype);
        const tirffctl = this.toTIRTypeKey(ffctl);

        return env.setResultExpressionInfo(new TIRTaskSelfControlExpression(exp.sinfo, tirtask, tirffctl), ffctl);
    }

    private checkTaskSelfAction(env: ExpressionTypeEnvironment, exp: TaskSelfActionExpression, refop: boolean): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk !== "write", "This code does not permit task operations (not a task method/action)");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        const mresolvetry = tsk.taskdecl.memberMethods.find((mm) => mm.name === exp.name);
        this.raiseErrorIf(exp.sinfo, mresolvetry === undefined, `Could not resolve method name "${exp.name}" from type ${tasktype.typeID}`);
        const mresolve = mresolvetry as MemberMethodDecl;

        this.raiseErrorIf(exp.sinfo, refop !== mresolve.invoke.isThisRef, "Cannot call a action/ref function in this expression position");

        this.raiseErrorIf(exp.sinfo, mresolve.invoke.terms.length !== exp.terms.length, "missing template types");
        let binds = new Map<string, ResolvedType>();
        for (let i = 0; i < mresolve.invoke.terms.length; ++i) {
            binds.set(mresolve.invoke.terms[i].name, this.normalizeTypeOnly(exp.terms[i], env.binds));
        }
        this.checkTemplateTypesOnInvoke(exp.sinfo, mresolve.invoke.terms, TemplateBindScope.createBaseBindScope(tsk.taskbinds), binds, mresolve.invoke.termRestrictions);

        const fdeclscope = TemplateBindScope.createBaseBindScope(tsk.taskbinds).pushScope(binds);
        const rtype = this.normalizeTypeOnly(mresolve.invoke.resultType, fdeclscope);
        const tirrtype = this.toTIRTypeKey(rtype);

        const tirdecltype = this.toTIRTypeKey(tasktype);

        const [argexps, fargs, pcl] = this.checkArgumentList(exp.sinfo, env.createFreshEnvExpressionFrom(), exp.args, mresolve.invoke.params, fdeclscope);
        let pcodes = new Map<string, { iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType }>();
        fargs.forEach((ee) => {
            pcodes.set(ee[0], { iscapture: false, pcode: ee[2], ftype: ee[1] });
        });

        const fkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, exp.name, mresolve.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)), pcl);
        const mldecl = new OOMemberLookupInfo<MemberMethodDecl>(tasktype, tsk.taskdecl, tsk.taskbinds, mresolve);
        this.m_pendingMethodMemberDecls.push({fkey: fkey, decl: mldecl, declaredecl: mldecl, binds: binds, pcodes: pcodes});

        this.raiseErrorIf(exp.sinfo, exp.isSelfRef !== mresolve.hasAttribute("ref"), `mismatch on self/this ref at callsite ${mresolve.name}`);

        if(mresolve.invoke.attributes.includes("task_action")) {
            return env.setResultExpressionInfo(new TIRCallMemberActionExpression(exp.sinfo, this.m_scratchCtr++, exp.name, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
        else if (mresolve.invoke.isThisRef) {
            return env.setResultExpressionInfo(new TIRCallMemberFunctionTaskSelfRefExpression(exp.sinfo, this.m_scratchCtr++, exp.name, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
        else {
            return env.setResultExpressionInfo(new TIRCallMemberFunctionTaskExpression(exp.sinfo, exp.name, fkey, tirrtype, this.toTIRTypeKey(tasktype), argexps), rtype);
        }
    }

    private checkTaskGetIDExpression(env: ExpressionTypeEnvironment, exp: TaskGetIDExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        return env.setResultExpressionInfo(new TIRTaskGetIDExpression(exp.sinfo, this.toTIRTypeKey(tasktype),  this.toTIRTypeKey(this.getSpecialTaskIDType())), this.getSpecialTaskIDType());
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
            case ExpressionTag.TaskSelfControlExpression: {
                return this.checkTaskAccessSelfControl(env, exp as TaskSelfControlExpression);
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

    private checkDeclareSingleVariableExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vname: string, isConst: boolean, decltype: TypeSignature, rhs: ExpressionTypeEnvironment | undefined): StatementTypeEnvironment {
        this.raiseErrorIf(sinfo, env.lookupLocalVar(vname) !== null, `${vname} cannot shadow previous definition`);

        const infertype = rhs !== undefined ? rhs.trepr : undefined;
        this.raiseErrorIf(sinfo, infertype === undefined && isConst, "must define const var at declaration site");
        this.raiseErrorIf(sinfo, infertype === undefined && decltype instanceof AutoTypeSignature, "must define auto typed var at declaration site");

        const vtype = (decltype instanceof AutoTypeSignature) ? infertype as ResolvedType : this.normalizeTypeOnly(decltype, env.binds);
        this.raiseErrorIf(sinfo, infertype !== undefined && !this.subtypeOf(infertype, vtype), `expression is not of declared type ${vtype.typeID}`);

        return env.addVar(vname, isConst, vtype, infertype !== undefined);
    }

    private checkAssignSingleVariableExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vname: string, rhs: ExpressionTypeEnvironment): StatementTypeEnvironment {
        const vinfo = env.lookupLocalVar(vname);
        this.raiseErrorIf(sinfo, vinfo === null, `Variable ${vname} was not previously defined`);
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, `Variable ${vname} is defined as const`);

        this.raiseErrorIf(sinfo, !this.subtypeOf(rhs.trepr, (vinfo as VarInfo).declaredType), `Assign value (${rhs.trepr.typeID}) is not subtype of declared variable type ${(vinfo as VarInfo).declaredType}`);

        return env.setVar(vname);
    }
    
    private checkEmptyStatement(env: StatementTypeEnvironment, stmt: EmptyStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return [env, []];
    }

    private checkVariableDeclarationStatement(env: StatementTypeEnvironment, stmt: VariableDeclarationStatement): [StatementTypeEnvironment, TIRStatement[]] {
        if(stmt.exp === undefined) {
            const declenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, undefined);

            return [declenv, [new TIRVarDeclareStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey((declenv.lookupLocalVar(stmt.name) as VarInfo).declaredType))]];
        }
        else {
            const itype = !(stmt.vtype instanceof AutoTypeSignature) ? this.normalizeTypeOnly(stmt.vtype, env.binds) : undefined;
            let rhs = this.checkExpressionAtAssign(env.createInitialEnvForExpressionEval(), stmt.exp, itype);

            assert(stmt.scinfo === undefined, "NOT IMPLEMENTED -- short-circuit return on assignment in type checker");

            let nstmt: TIRStatement[] = [];
            let nenv: StatementTypeEnvironment | undefined = undefined;
            if(rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, rhs);

                const dvtype = (nenv.lookupLocalVar(stmt.name) as VarInfo).declaredType;
                const refv = rhs.expressionResult.thisref;
                const refvinfotry = env.lookupLocalVar(refv);
                this.raiseErrorIf(stmt.sinfo, refvinfotry === null || refvinfotry.isConst, `cannot modify variable ${refv} as ref`);
                const refvinfo = refvinfotry as VarInfo;

                const tirda = this.emitCoerceIfNeeded(rhs.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rhs.trepr), rhs.expressionResult.scidx), rhs.trepr), stmt.sinfo, dvtype);

                nstmt = [
                    new TIRCallStatementWRef(stmt.sinfo, rhs.expressionResult, rhs.expressionResult.etype, this.toTIRTypeKey(refvinfo.declaredType), rhs.expressionResult.scidx),
                    new TIRVarRefAssignFromScratch(stmt.sinfo, refv, this.toTIRTypeKey(refvinfo.declaredType), rhs.expressionResult.scidx),
                    new TIRVarDeclareAndAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), tirda.expressionResult, stmt.isConst)
                ];
            }
            else if (rhs.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, rhs);

                const dvtype = (nenv.lookupLocalVar(stmt.name) as VarInfo).declaredType;
                const taskinfo = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
                const refvinfo = ResolvedType.createSingle(ResolvedTaskAtomType.create(taskinfo.taskdecl, taskinfo.taskbinds));

                const tirda = this.emitCoerceIfNeeded(rhs.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rhs.trepr), rhs.expressionResult.scidx), rhs.trepr), stmt.sinfo, dvtype);

                nstmt = [
                    new TIRCallStatementWTaskRef(stmt.sinfo, rhs.expressionResult, rhs.expressionResult.etype, this.toTIRTypeKey(refvinfo), rhs.expressionResult.scidx),
                    new TIRTaskRefAssignFromScratch(stmt.sinfo, this.toTIRTypeKey(refvinfo), rhs.expressionResult.scidx),
                    new TIRVarDeclareAndAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), tirda.expressionResult, stmt.isConst)
                ];
            }
            else if (rhs.expressionResult instanceof TIRCallMemberActionExpression) {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, rhs);

                const dvtype = (nenv.lookupLocalVar(stmt.name) as VarInfo).declaredType;
                const taskinfo = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
                const refvinfo = ResolvedType.createSingle(ResolvedTaskAtomType.create(taskinfo.taskdecl, taskinfo.taskbinds));

                const tirda = this.emitCoerceIfNeeded(rhs.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rhs.trepr), rhs.expressionResult.scidx), rhs.trepr), stmt.sinfo, dvtype);

                nstmt = [
                    new TIRCallStatementWAction(stmt.sinfo, rhs.expressionResult, rhs.expressionResult.etype, this.toTIRTypeKey(refvinfo), rhs.expressionResult.scidx),
                    new TIRTaskRefAssignFromScratch(stmt.sinfo, this.toTIRTypeKey(refvinfo), rhs.expressionResult.scidx),
                    new TIRVarDeclareAndAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), tirda.expressionResult, stmt.isConst)
                ];
            }
            else {
                nenv = this.checkDeclareSingleVariableExplicit(stmt.sinfo, env, stmt.name, stmt.isConst, stmt.vtype, rhs);

                const dvtype = (nenv.lookupLocalVar(stmt.name) as VarInfo).declaredType;
                const rhsconv = this.emitCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

                nstmt = [new TIRVarDeclareAndAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult, stmt.isConst)];
            }
            
            return [nenv, nstmt];
        }
    }

    private checkVariableAssignStatement(env: StatementTypeEnvironment, stmt: VariableAssignmentStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, env.lookupLocalVar(stmt.name) === null, `variable ${stmt.name} not previously declared`);
        let rhs = this.checkExpressionAtAssign(env.createInitialEnvForExpressionEval(), stmt.exp, (env.lookupLocalVar(stmt.name) as VarInfo).declaredType);

        assert(stmt.scinfo === undefined, "NOT IMPLEMENTED -- short-circuit return on assignment in type checker");

        let nstmt: TIRStatement[] = [];
        let nenv: StatementTypeEnvironment | undefined = undefined;
        if (rhs.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, rhs);

            const dvtype = (nenv.lookupLocalVar(stmt.name) as VarInfo).declaredType;
            const refv = rhs.expressionResult.thisref;
            const refvinfotry = env.lookupLocalVar(refv);
            this.raiseErrorIf(stmt.sinfo, refvinfotry === null || refvinfotry.isConst, `cannot modify variable ${refv} as ref`);
            const refvinfo = refvinfotry as VarInfo;

            const tirda = this.emitCoerceIfNeeded(rhs.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rhs.trepr), rhs.expressionResult.scidx), rhs.trepr), stmt.sinfo, dvtype);

            nstmt = [
                new TIRCallStatementWRef(stmt.sinfo, rhs.expressionResult, rhs.expressionResult.etype, this.toTIRTypeKey(refvinfo.declaredType), rhs.expressionResult.scidx),
                new TIRVarRefAssignFromScratch(stmt.sinfo, refv, this.toTIRTypeKey(refvinfo.declaredType), rhs.expressionResult.scidx),
                new TIRVarAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), tirda.expressionResult)
            ];
        }
        else if (rhs.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, rhs);

            const dvtype = (nenv.lookupLocalVar(stmt.name) as VarInfo).declaredType;
            const taskinfo = this.m_taskType as { taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType> };
            const refvinfo = ResolvedType.createSingle(ResolvedTaskAtomType.create(taskinfo.taskdecl, taskinfo.taskbinds));

            const tirda = this.emitCoerceIfNeeded(rhs.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rhs.trepr), rhs.expressionResult.scidx), rhs.trepr), stmt.sinfo, dvtype);

            nstmt = [
                new TIRCallStatementWTaskRef(stmt.sinfo, rhs.expressionResult, rhs.expressionResult.etype, this.toTIRTypeKey(refvinfo), rhs.expressionResult.scidx),
                new TIRTaskRefAssignFromScratch(stmt.sinfo, this.toTIRTypeKey(refvinfo), rhs.expressionResult.scidx),
                new TIRVarAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), tirda.expressionResult)
            ];
        }
        else if (rhs.expressionResult instanceof TIRCallMemberActionExpression) {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, rhs);

            const dvtype = (nenv.lookupLocalVar(stmt.name) as VarInfo).declaredType;
            const taskinfo = this.m_taskType as { taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType> };
            const refvinfo = ResolvedType.createSingle(ResolvedTaskAtomType.create(taskinfo.taskdecl, taskinfo.taskbinds));

            const tirda = this.emitCoerceIfNeeded(rhs.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rhs.trepr), rhs.expressionResult.scidx), rhs.trepr), stmt.sinfo, dvtype);

            nstmt = [
                new TIRCallStatementWAction(stmt.sinfo, rhs.expressionResult, rhs.expressionResult.etype, this.toTIRTypeKey(refvinfo), rhs.expressionResult.scidx),
                new TIRTaskRefAssignFromScratch(stmt.sinfo, this.toTIRTypeKey(refvinfo), rhs.expressionResult.scidx),
                new TIRVarAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), tirda.expressionResult)
            ];
        }
        else {
            nenv = this.checkAssignSingleVariableExplicit(stmt.sinfo, env, stmt.name, rhs);

            const dvtype = (nenv.lookupLocalVar(stmt.name) as VarInfo).declaredType;
            const rhsconv = this.emitCoerceIfNeeded(rhs, stmt.exp.sinfo, dvtype);

            nstmt = [new TIRVarAssignStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(dvtype), rhsconv.expressionResult)];
        }

        return [nenv, nstmt];
    }

    private checkVariableRetypeStatement(env: StatementTypeEnvironment, stmt: VariableRetypeStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const vinfotry = env.lookupLocalVar(stmt.name);
        this.raiseErrorIf(stmt.sinfo, vinfotry === null, "cannot retype captured variables");
        const vinfo = vinfotry as VarInfo;

        const testinfo = this.processITestAsTestOp(stmt.sinfo, vinfo.declaredType, vinfo.declaredType, new TIRAccessVariableExpression(stmt.sinfo, stmt.name, this.toTIRTypeKey(vinfo.declaredType)), stmt.ttest, env.binds);
        const asinfo = this.processITestAsConvertOp(stmt.sinfo, vinfo.declaredType, vinfo.declaredType, new TIRAccessVariableExpression(stmt.sinfo, stmt.name, this.toTIRTypeKey(vinfo.declaredType)), stmt.ttest, env.binds, false);
        this.raiseErrorIf(stmt.sinfo, !testinfo.hastrueflow, "variable retype operation will always fail");

        return [
            env.setVarFlowType(stmt.name, asinfo.trueflow as ResolvedType),
            [new TIRVariableRetypeStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(vinfo.declaredType), this.toTIRTypeKey(asinfo.trueflow as ResolvedType), asinfo.asexp as TIRExpression)]
        ]
    }

    private checkExpressionSCReturnStatement(env: StatementTypeEnvironment, stmt: ExpressionSCReturnStatement): [StatementTypeEnvironment, TIRStatement[]] {
        if(stmt.ttest instanceof Expression) {
            assert(false, "NOT IMPLEMENTED -- short-circuit return statement in type checker");
        }
        else {
            assert(false, "NOT IMPLEMENTED -- short-circuit return statement in type checker");
        }

        //TODO: also see the SC return in assign code -- probably want common handling for eval expression + check flows in both cases
        //---- see the TIRScratchSCRetypeStatement opcode for handling this -- assign result to var (or scratch in ref assign), process with SC opcode, and then do assign (or nothing) as needed
        return [env, [new TIRAbortStatement(stmt.sinfo, "Not implemented -- short-circuit")]];
    }
    
    private checkVariableSCRetypeStatement(env: StatementTypeEnvironment, stmt: VariableSCRetypeStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const vinfotry = env.lookupLocalVar(stmt.name);
        this.raiseErrorIf(stmt.sinfo, vinfotry === null, "cannot retype captured variables");
        const vinfo = vinfotry as VarInfo;

        const testinfo = this.processITestAsTestOp(stmt.sinfo, vinfo.declaredType, vinfo.declaredType, new TIRAccessVariableExpression(stmt.sinfo, stmt.name, this.toTIRTypeKey(vinfo.declaredType)), stmt.ttest, env.binds);
        const asinfo = this.processITestAsConvertOp(stmt.sinfo, vinfo.declaredType, vinfo.declaredType, new TIRAccessVariableExpression(stmt.sinfo, stmt.name, this.toTIRTypeKey(vinfo.declaredType)), stmt.ttest, env.binds, true);
        
        this.raiseErrorIf(stmt.sinfo, testinfo.falseflow === undefined, "variable retypr operation is always successful");
        this.raiseErrorIf(stmt.sinfo, !testinfo.hastrueflow, "variable retype operation will always fail");

        let binderinfo: [TIRExpression, string] | undefined = undefined;
        let retflow: TIRExpression | undefined = undefined;
        if(stmt.res === undefined) {
            retflow = this.emitCoerceIfNeeded(env.createInitialEnvForExpressionEval().setResultExpressionInfo(asinfo.asnotexp as TIRExpression, asinfo.falseflow as ResolvedType), stmt.sinfo, this.m_rtype).expressionResult;
        }
        else {
            if(stmt.binderinfo === undefined) {
                const eenv = this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.res, this.m_rtype);
                retflow = this.emitCoerceIfNeeded(eenv, stmt.res.sinfo, this.m_rtype).expressionResult;
            }
            else {
                binderinfo = [asinfo.asnotexp as TIRExpression, stmt.binderinfo as string];

                const eenv = this.checkExpression(env.createInitialEnvForExpressionEval().pushBinderFrame(stmt.binderinfo, asinfo.falseflow as ResolvedType), stmt.res, this.m_rtype);
                retflow = this.emitCoerceIfNeeded(eenv, stmt.res.sinfo, this.m_rtype).expressionResult;
            }
        }

        return [
            env.setVarFlowType(stmt.name, asinfo.trueflow as ResolvedType),
            [new TIRVariableSCRetypeStatement(stmt.sinfo, stmt.name, this.toTIRTypeKey(vinfo.declaredType), testinfo.testexp, asinfo.asexp as TIRExpression, retflow as TIRExpression, binderinfo)]
        ];
    }

    private checkRefCallStatement(env: StatementTypeEnvironment, stmt: RefCallStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const ee = this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.call, undefined);

        if (ee.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
            const refvtype = (env.lookupLocalVar(ee.expressionResult.thisref) as VarInfo).declaredType;
            return [env, [new TIRCallStatementWRef(stmt.sinfo, ee.expressionResult, ee.expressionResult.etype, this.toTIRTypeKey(refvtype), this.m_scratchCtr++)]];
        }
        else if (ee.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
            return [env, [new TIRCallStatementWTaskRef(stmt.sinfo, ee.expressionResult, ee.expressionResult.etype, ee.expressionResult.tsktype, this.m_scratchCtr++)]];
        }
        else if (ee.expressionResult instanceof TIRCallMemberActionExpression) {
            return [env, [new TIRCallStatementWAction(stmt.sinfo, ee.expressionResult, ee.expressionResult.etype, ee.expressionResult.tsktype, this.m_scratchCtr++)]];
        }
        else {
            this.raiseError(stmt.sinfo, `Unknown op kind ${ee.expressionResult.tag}`);
            return [env, [new TIRNopStatement(stmt.sinfo)]];
        }
    } 

    private checkReturnStatement(env: StatementTypeEnvironment, stmt: ReturnStatement): [StatementTypeEnvironment, TIRStatement[]] {
        let rexp: TIRStatement[] | undefined = undefined;
        let rval = this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.value, this.m_rtype);

        if (rval.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
            const tirda = this.emitCoerceIfNeeded(rval.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rval.trepr), rval.expressionResult.scidx), rval.trepr), stmt.sinfo, this.m_rtype);

            const refv = rval.expressionResult.thisref;
            const refvinfotry = env.lookupLocalVar(refv) ;
            this.raiseErrorIf(stmt.sinfo, refvinfotry === null || refvinfotry.isConst, `cannot modify variable ${refv} as ref`);
            const refvinfo = refvinfotry as VarInfo;

            rexp = [
                new TIRCallStatementWRef(stmt.sinfo, rval.expressionResult, rval.expressionResult.etype, this.toTIRTypeKey(refvinfo.declaredType), rval.expressionResult.scidx),
                new TIRVarRefAssignFromScratch(stmt.sinfo, refv, this.toTIRTypeKey(refvinfo.declaredType), rval.expressionResult.scidx)
            ];
            rval = tirda;
        }
        else if (rval.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
            const taskinfo = this.m_taskType as { taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType> };
            const refvinfo = ResolvedType.createSingle(ResolvedTaskAtomType.create(taskinfo.taskdecl, taskinfo.taskbinds));

            const tirda = this.emitCoerceIfNeeded(rval.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rval.trepr), rval.expressionResult.scidx), rval.trepr), stmt.sinfo, this.m_rtype);

            rexp = [
                new TIRCallStatementWTaskRef(stmt.sinfo, rval.expressionResult, rval.expressionResult.etype, this.toTIRTypeKey(refvinfo), rval.expressionResult.scidx),
                new TIRTaskRefAssignFromScratch(stmt.sinfo, this.toTIRTypeKey(refvinfo), rval.expressionResult.scidx)
            ];
            rval = tirda;
        }
        else if (rval.expressionResult instanceof TIRCallMemberActionExpression) {
            const taskinfo = this.m_taskType as { taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType> };
            const refvinfo = ResolvedType.createSingle(ResolvedTaskAtomType.create(taskinfo.taskdecl, taskinfo.taskbinds));

            const tirda = this.emitCoerceIfNeeded(rval.setResultExpressionInfo(new TIRAccessScratchIndexExpression(stmt.sinfo, 1, this.toTIRTypeKey(rval.trepr), rval.expressionResult.scidx), rval.trepr), stmt.sinfo, this.m_rtype);

            rexp = [
                new TIRCallStatementWAction(stmt.sinfo, rval.expressionResult, rval.expressionResult.etype, this.toTIRTypeKey(refvinfo), rval.expressionResult.scidx),
                new TIRTaskRefAssignFromScratch(stmt.sinfo, this.toTIRTypeKey(refvinfo), rval.expressionResult.scidx)
            ];
            rval = tirda;
        }
        else {
            rexp = [];
            rval = this.emitCoerceIfNeeded(rval, stmt.sinfo, this.m_rtype);
        }

        if(this.m_returnMode === ReturnMode.Standard) {
            rexp.push(new TIRReturnStatement(stmt.sinfo, rval.expressionResult));
        }
        else if(this.m_returnMode === ReturnMode.MemberRef) {
            rexp.push(new TIRReturnStatementWRef(stmt.sinfo, rval.expressionResult));
        }
        else if(this.m_returnMode === ReturnMode.MemberSelf) {
            rexp.push(new TIRReturnStatementWTaskRef(stmt.sinfo, rval.expressionResult));
        }
        else {
            rexp.push(new TIRReturnStatementWAction(stmt.sinfo, rval.expressionResult));
        }

        return [env.endOfExecution(), rexp as TIRStatement[]];
    }

    private checkAbortStatement(env: StatementTypeEnvironment, stmt: AbortStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return [env.endOfExecution(), [new TIRAbortStatement(stmt.sinfo, "Abort")]];
    }

    private checkAssertStatement(env: StatementTypeEnvironment, stmt: AssertStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const test = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.cond, this.getSpecialBoolType()), stmt.sinfo, this.getSpecialBoolType());

        if (!isBuildLevelEnabled(stmt.level, this.m_buildLevel)) {
            return [env, []];
        }
        else {
            const astmt = new TIRAssertCheckStatement(stmt.sinfo, test.expressionResult, `Assertion failed -- ${path.basename(this.m_file)} : ${stmt.sinfo.line}`);
            return [env, [astmt]];
        }
    }

    private checkDebugStatement(env: StatementTypeEnvironment, stmt: DebugStatement): [StatementTypeEnvironment, TIRStatement[]] {
        if (this.m_buildLevel !== "debug") {
            return [env, []];
        }
        else {
            return [env, [new TIRDebugStatement(stmt.sinfo, this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.value, undefined).expressionResult)]];
        }
    }

    private mergeVarTypeMaps(envs: StatementTypeEnvironment[]): Map<string, ResolvedType> {
        let rrm = new Map<string, ResolvedType[]>();
        envs.forEach((eev) => {
            eev.args.forEach((ai, an) => {
                if(!rrm.has(an)) {
                    rrm.set(an, []);
                }
                if((rrm.get(an) as ResolvedType[]).find((tt) => tt.typeID === ai.declaredType.typeID) === undefined) {
                    (rrm.get(an) as ResolvedType[]).push(ai.declaredType);
                }
            });

            eev.locals.forEach((lf) => {
                lf.forEach((vi, vn) => {
                    if(!rrm.has(vn)) {
                        rrm.set(vn, []);
                    }
                    if((rrm.get(vn) as ResolvedType[]).find((tt) => tt.typeID === vi.declaredType.typeID) === undefined) {
                        (rrm.get(vn) as ResolvedType[]).push(vi.declaredType);
                    }
                });
            });
        });

        let mrm = new Map<string, ResolvedType>();
        rrm.forEach((tl, vn) => {
            const tt = this.normalizeUnionList(tl);
            mrm.set(vn, tt);
        });

        return mrm;
    }

    private emitVarRetypeAtFlowJoin(sinfo: SourceInfo, env: StatementTypeEnvironment, remap: Map<string, ResolvedType>): {vname: string, cast: TIRExpression}[] {
        let vrl: {vname: string, vtype: ResolvedType}[] = [];
        remap.forEach((tt, vn) => {
            const vvinfo = env.lookupLocalVar(vn) as VarInfo;
            if(vvinfo.declaredType.typeID !== tt.typeID) {
                vrl.push({vname: vn, vtype: tt});
            }
        });
        vrl.sort((a, b) => a.vname.localeCompare(b.vname));

        if(vrl.length === 0) {
            return [];
        }
        else {
            const rmps = vrl.map((rp) => {
                const vvinfo = env.lookupLocalVar(rp.vname) as VarInfo;
                const varenv = env.createInitialEnvForExpressionEval().setResultExpressionInfo(new TIRAccessVariableExpression(sinfo, rp.vname, this.toTIRTypeKey(vvinfo.declaredType)), vvinfo.declaredType);
                const aswrk = this.emitCoerceIfNeeded_NoCheck(varenv, sinfo, rp.vtype).expressionResult;
                    
                return {vname: rp.vname, cast: aswrk};
            });

            return rmps;
        }
    }

    private checkIfStatement(env: StatementTypeEnvironment, stmt: IfStatement): [StatementTypeEnvironment, TIRStatement[]] {
        let results: {test: ExpressionTypeEnvironment, blck: TIRScopedBlockStatement, fenv: StatementTypeEnvironment, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined}[] = [];

        let testflowtypes = new Map<string, ResolvedType>();
        let elsebind: [TIRExpression, ResolvedType] | undefined | null = undefined;

        for (let i = 0; i < stmt.condflow.length; ++i) {
            if(stmt.condflow[i].cond.itestopt === undefined) {
                const tenv = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.condflow[i].cond.exp, this.getSpecialBoolType()), stmt.condflow[i].cond.exp.sinfo, this.getSpecialBoolType());
                elsebind = null;

                this.raiseErrorIf(stmt.condflow[i].value.sinfo, stmt.condflow[i].binderinfo !== undefined, "Binder doesn't make sense here -- will be bound to true");
                
                const [resenv, blck] = this.checkScopedBlockStatement(env, stmt.condflow[i].value);
                results.push({ test: tenv, blck: blck, fenv: resenv, binderinfo: undefined });
            }
            else {
                const eenv = this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.condflow[i].cond.exp, undefined);
                const eenvflowtype = testflowtypes.get(eenv.expressionResult.expstr) || eenv.trepr;

                if(elsebind === null) {
                    elsebind = null;
                }
                else if(elsebind === undefined) {
                    elsebind = [eenv.expressionResult, eenv.trepr];
                }
                else {
                    elsebind = (elsebind[0].expstr === eenv.expressionResult.expstr) ? elsebind : null;
                }

                if(stmt.condflow[i].binderinfo === undefined) {
                    const testinfo = this.processITestAsTestOp(stmt.condflow[i].cond.exp.sinfo, eenv.trepr, eenvflowtype, eenv.expressionResult, stmt.condflow[i].cond.itestopt as ITest, eenv.binds);
                    this.raiseErrorIf(stmt.condflow[i].cond.exp.sinfo, testinfo.falseflow === undefined, `test always evaluates to true`);
                    this.raiseErrorIf(stmt.condflow[i].cond.exp.sinfo, !testinfo.hastrueflow, `test always evaluates to false`);  

                    const [resenv, resblck] = this.checkScopedBlockStatement(env, stmt.condflow[i].value);
                    
                    testflowtypes.set(eenv.expressionResult.expstr, testinfo.falseflow as ResolvedType);
                    results.push({ test: eenv.setResultExpressionInfo(testinfo.testexp, this.getSpecialBoolType()), blck: resblck, fenv: resenv, binderinfo: undefined });
                }
                else {
                    const scratchidx = this.m_scratchCtr++;
                    const testinfo = this.processITestAsTestOp(stmt.condflow[i].cond.exp.sinfo, eenv.trepr, eenvflowtype, new TIRAccessScratchSingleValueExpression(stmt.condflow[i].cond.exp.sinfo, this.toTIRTypeKey(eenv.trepr), scratchidx), stmt.condflow[i].cond.itestopt as ITest, eenv.binds);
                    const asinfo = this.processITestAsConvertOp(stmt.condflow[i].value.sinfo, eenv.trepr, eenvflowtype, new TIRAccessScratchSingleValueExpression(stmt.condflow[i].cond.exp.sinfo, this.toTIRTypeKey(eenv.trepr), scratchidx), stmt.condflow[i].cond.itestopt as ITest, eenv.binds, true);
                    const bindtype = asinfo.trueflow as ResolvedType;

                    this.raiseErrorIf(stmt.condflow[i].cond.exp.sinfo, testinfo.falseflow === undefined, `test always evaluates to true`);
                    this.raiseErrorIf(stmt.condflow[i].cond.exp.sinfo, !testinfo.hastrueflow, `test always evaluates to false`);

                    const flowenv = env.pushLocalScope().addVar(stmt.condflow[i].binderinfo as string, true, bindtype, true);
                    const [resenv, resblck] = this.checkScopedBlockStatement(flowenv, stmt.condflow[i].value);

                    testflowtypes.set(eenv.expressionResult.expstr, testinfo.falseflow as ResolvedType);
                    results.push({ test: eenv.setResultExpressionInfo(testinfo.testexp, this.getSpecialBoolType()), blck: resblck, fenv: resenv.popLocalScope(), binderinfo: [eenv.expressionResult, scratchidx, asinfo.asexp as TIRExpression, stmt.condflow[i].binderinfo as string]});
                }
            }
        }

        if (stmt.elseflow === undefined) {
            results.push({ test: env.createInitialEnvForExpressionEval().setResultExpressionInfo(new TIRLiteralBoolExpression(stmt.sinfo, true), this.getSpecialBoolType()), blck: new TIRScopedBlockStatement([], false), fenv: env, binderinfo: undefined});
        }
        else {
            if (stmt.elseflow.binderinfo === undefined) {
                const [resenv, resblck] = this.checkScopedBlockStatement(env, stmt.elseflow.value);
                results.push({ test: env.createInitialEnvForExpressionEval().setResultExpressionInfo(new TIRLiteralBoolExpression(stmt.sinfo, true), this.getSpecialBoolType()), blck: resblck, fenv: resenv, binderinfo: undefined });
            }
            else {
                this.raiseErrorIf(stmt.elseflow.value.sinfo, elsebind === undefined || elsebind === null, "cannot use binder in else unless all previous clauses test same expression and use ITests");

                const scratchidx = this.m_scratchCtr++;
                const [elseexpr, elsetype] = elsebind as [TIRExpression, ResolvedType];
                const bindtype = testflowtypes.get(elseexpr.expstr) as ResolvedType;

                const flowenv = env.pushLocalScope().addVar(stmt.elseflow.binderinfo as string, true, bindtype, true);
                const [resenv, resblck] = this.checkScopedBlockStatement(flowenv, stmt.elseflow.value);

                const bindexp = this.emitCoerceIfNeeded_NoCheck(env.createInitialEnvForExpressionEval().setResultExpressionInfo(new TIRAccessScratchSingleValueExpression(stmt.elseflow.value.sinfo, this.toTIRTypeKey(elsetype), scratchidx), elsetype), stmt.elseflow.value.sinfo, bindtype).expressionResult;
                results.push({ test: env.createInitialEnvForExpressionEval().setResultExpressionInfo(new TIRLiteralBoolExpression(stmt.sinfo, true), this.getSpecialBoolType()), blck: resblck, fenv: resenv.popLocalScope(), binderinfo: [elseexpr as TIRExpression, scratchidx, bindexp, stmt.elseflow.binderinfo as string] });
            }
        }
        const mvinfo = this.mergeVarTypeMaps(results.filter((rr) => !rr.blck.isterminal).map((rr) => rr.fenv));

        const ifcl = {test: results[0].test.expressionResult, value: results[0].blck, binderinfo: results[0].binderinfo, recasttypes: this.emitVarRetypeAtFlowJoin(stmt.sinfo, results[0].fenv, mvinfo)};

        const elifcl = results.slice(1, results.length - 1).map((rr) => {
            return {test: rr.test.expressionResult, value: rr.blck, binderinfo: rr.binderinfo, recasttypes: this.emitVarRetypeAtFlowJoin(stmt.sinfo, rr.fenv, mvinfo)};
        });
        
        const elsecl = {value: results[results.length - 1].blck, binderinfo: results[results.length - 1].binderinfo, recasttypes: this.emitVarRetypeAtFlowJoin(stmt.sinfo, results[results.length - 1].fenv, mvinfo)};

        const rexp = new TIRIfStatement(stmt.sinfo, ifcl, elifcl, elsecl);
        const rflows = [...results.map((ff) => ff.fenv)].filter((es) => !es.isDeadFlow);
        if(rflows.length === 0) {
            return [env.endOfExecution(), [rexp]];
        }
        else {
            const jenv = env.updateFlowAtJoin(mvinfo, rflows);
            return [jenv, [rexp]];
        }
    }

    private checkSwitchStatement(env: StatementTypeEnvironment, stmt: SwitchStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const venv = this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.sval, undefined);
        
        const scratchidx = this.m_scratchCtr++;
        let ctype: ResolvedType = venv.trepr;
        let exhaustive = false;
        let results: {test: TIRExpression | undefined, blck: TIRScopedBlockStatement, fenv: StatementTypeEnvironment, binderinfo: [TIRExpression, string] | undefined}[] = [];

        for (let i = 0; i < stmt.switchflow.length; ++i) {
            //it is a wildcard match
            if(stmt.switchflow[i].condlit === undefined) {
                this.raiseErrorIf(stmt.sinfo, i !== stmt.switchflow.length - 1, `wildcard should be last option in switch expression but there were ${stmt.switchflow.length - (i + 1)} more that are unreachable`);

                let senv = env;
                let binderinfo: [TIRExpression, string] | undefined = undefined;
                if (stmt.switchflow[i].binderinfo !== undefined) {
                    binderinfo = [this.generateCoerceExpForITestConv(new TIRAccessScratchSingleValueExpression(stmt.switchflow[i].value.sinfo, this.toTIRTypeKey(venv.trepr), scratchidx), venv.trepr, stmt.switchflow[i].value.sinfo, ctype), stmt.switchflow[i].binderinfo as string];
                    senv = senv.pushLocalScope().addVar(stmt.switchflow[i].binderinfo as string, true, ctype, true);
                }
                const trueenv = this.checkScopedBlockStatement(senv, stmt.switchflow[i].value);

                results.push({test: undefined, blck: trueenv[1], fenv: binderinfo !== undefined ? trueenv[0].popLocalScope() : trueenv[0], binderinfo: binderinfo});

                exhaustive = true;
                break;
            }
            else {
                const condsinfo = (stmt.switchflow[i].condlit as LiteralExpressionValue).exp.sinfo;

                const test = this.processITestAsTestOp(condsinfo, venv.trepr, ctype, new TIRAccessScratchSingleValueExpression(condsinfo, this.toTIRTypeKey(venv.trepr), scratchidx), new ITestLiteral(false, stmt.switchflow[i].condlit as LiteralExpressionValue), venv.binds);
                this.raiseErrorIf(condsinfo, !test.hastrueflow, "test is always false");
                this.raiseErrorIf(condsinfo, i !== stmt.switchflow.length - 1 && test.falseflow === undefined, "test is always true (and cases below will never be reached)");
                
                const conv = this.processITestAsConvertOp(condsinfo, venv.trepr, ctype, new TIRAccessScratchSingleValueExpression(condsinfo, this.toTIRTypeKey(venv.trepr), scratchidx), new ITestLiteral(false, stmt.switchflow[i].condlit as LiteralExpressionValue), venv.binds, true);
                ctype = test.falseflow as ResolvedType;

                let senv = env;
                let binderinfo: [TIRExpression, string] | undefined = undefined;
                if (stmt.switchflow[i].binderinfo !== undefined) {
                    binderinfo = [conv.asexp as TIRExpression, stmt.switchflow[i].binderinfo as string];
                    senv = senv.pushLocalScope().addVar(stmt.switchflow[i].binderinfo as string, true, conv.trueflow as ResolvedType, true);
                }
                const trueenv = this.checkScopedBlockStatement(senv, stmt.switchflow[i].value);
                
                results.push({test: test.testexp, blck: trueenv[1], fenv: binderinfo !== undefined ? trueenv[0].popLocalScope() : trueenv[0], binderinfo: binderinfo});
            }
        }
        const mvinfo = this.mergeVarTypeMaps(results.filter((rr) => !rr.blck.isterminal).map((rr) => rr.fenv));

        const clauses = results
            .filter((ffp) => ffp.test !== undefined)
            .map((ffp) => {
                return {match: ffp.test as TIRExpression, value: ffp.blck, binderinfo: ffp.binderinfo, recasttypes: this.emitVarRetypeAtFlowJoin(stmt.sinfo, ffp.fenv, mvinfo)};
            });
        const edefault = results.find((ffp) => ffp.test === undefined) ? {value: results[results.length - 1].blck, binderinfo: results[results.length - 1].binderinfo, recasttypes: this.emitVarRetypeAtFlowJoin(stmt.sinfo, results[results.length - 1].fenv, mvinfo)} : undefined;

        const rexp = new TIRSwitchStatement(stmt.sinfo, venv.expressionResult, scratchidx, clauses, edefault, exhaustive || ctype === undefined);

        const rflows = [...results.map((ff) => ff.fenv)].filter((es) => !es.isDeadFlow);
        if(rflows.length === 0) {
            return [env.endOfExecution(), [rexp]];
        }
        else {
            const jenv = env.updateFlowAtJoin(mvinfo, rflows);
            return [jenv, [rexp]];
        }
    }

    private checkMatchStatement(env: StatementTypeEnvironment, stmt: MatchStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const venv = this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.sval, undefined);
        
        const scratchidx = this.m_scratchCtr++;
        let ctype: ResolvedType = venv.trepr;
        let exhaustive = false;
        let results: {test: TIRExpression | undefined, blck: TIRScopedBlockStatement, fenv: StatementTypeEnvironment, binderinfo: [TIRExpression, string] | undefined}[] = [];

        for (let i = 0; i < stmt.matchflow.length; ++i) {
            //it is a wildcard match
            if(stmt.matchflow[i].mtype === undefined) {
                this.raiseErrorIf(stmt.sinfo, i !== stmt.matchflow.length - 1, `wildcard should be last option in switch expression but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);

                let senv = env;
                let binderinfo: [TIRExpression, string] | undefined = undefined;
                if (stmt.matchflow[i].binderinfo !== undefined) {
                    binderinfo = [this.generateCoerceExpForITestConv(new TIRAccessScratchSingleValueExpression(stmt.matchflow[i].value.sinfo, this.toTIRTypeKey(venv.trepr), scratchidx), venv.trepr, stmt.matchflow[i].value.sinfo, ctype), stmt.matchflow[i].binderinfo as string];
                    senv = senv.pushLocalScope().addVar(stmt.matchflow[i].binderinfo as string, true, ctype, true);
                }
                const trueenv = this.checkScopedBlockStatement(senv, stmt.matchflow[i].value);

                results.push({test: undefined, blck: trueenv[1], fenv: binderinfo !== undefined ? trueenv[0].popLocalScope() : trueenv[0], binderinfo: binderinfo});

                exhaustive = true;
                break;
            }
            else {
                const condsinfo = (stmt.matchflow[i].mtype as TypeSignature).sinfo;

                const test = this.processITestAsTestOp(condsinfo, venv.trepr, ctype, new TIRAccessScratchSingleValueExpression(condsinfo, this.toTIRTypeKey(venv.trepr), scratchidx), new ITestType(false, stmt.matchflow[i].mtype as TypeSignature), venv.binds);
                this.raiseErrorIf(condsinfo, !test.hastrueflow, "test is always false");
                this.raiseErrorIf(condsinfo, i !== stmt.matchflow.length - 1 && test.falseflow === undefined, "test is always true (and cases below will never be reached)");
                
                const conv = this.processITestAsConvertOp(condsinfo, venv.trepr, ctype, new TIRAccessScratchSingleValueExpression(condsinfo, this.toTIRTypeKey(venv.trepr), scratchidx), new ITestType(false, stmt.matchflow[i].mtype as TypeSignature), venv.binds, true);
                ctype = test.falseflow as ResolvedType;

                let senv = env;
                let binderinfo: [TIRExpression, string] | undefined = undefined;
                if (stmt.matchflow[i].binderinfo !== undefined) {
                    binderinfo = [conv.asexp as TIRExpression, stmt.matchflow[i].binderinfo as string];
                    senv = senv.pushLocalScope().addVar(stmt.matchflow[i].binderinfo as string, true, conv.trueflow as ResolvedType, true);
                }
                const trueenv = this.checkScopedBlockStatement(senv, stmt.matchflow[i].value);
                
                results.push({test: test.testexp, blck: trueenv[1], fenv: binderinfo !== undefined ? trueenv[0].popLocalScope() : trueenv[0], binderinfo: binderinfo});
            }
        }
        const mvinfo = this.mergeVarTypeMaps(results.filter((rr) => !rr.blck.isterminal).map((rr) => rr.fenv));

        const clauses = results
            .filter((ffp) => ffp.test !== undefined)
            .map((ffp) => {
                return {match: ffp.test as TIRExpression, value: ffp.blck, binderinfo: ffp.binderinfo, recasttypes: this.emitVarRetypeAtFlowJoin(stmt.sinfo, ffp.fenv, mvinfo)};
            });
        const edefault = results.find((ffp) => ffp.test === undefined) ? {value: results[results.length - 1].blck, binderinfo: results[results.length - 1].binderinfo, recasttypes: this.emitVarRetypeAtFlowJoin(stmt.sinfo, results[results.length - 1].fenv, mvinfo)} : undefined;

        const rexp = new TIRMatchStatement(stmt.sinfo, venv.expressionResult, scratchidx, clauses, edefault, exhaustive || ctype === undefined);
        
        const rflows = [...results.map((ff) => ff.fenv)].filter((es) => !es.isDeadFlow);
        if(rflows.length === 0) {
            return [env.endOfExecution(), [rexp]];
        }
        else {
            const jenv = env.updateFlowAtJoin(mvinfo, rflows);
            return [jenv, [rexp]];
        }
    }

    private checkEnvironmentFreshStatement(env: StatementTypeEnvironment, stmt: EnvironmentFreshStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const assigns = stmt.assigns.map((asgn) => {
            this.raiseErrorIf(stmt.sinfo, asgn.valexp === undefined, "cannot clear key in fresh environment creation");

            const etype = this.normalizeTypeOnly((asgn.valexp as [TypeSignature, Expression])[0], env.binds);
            const easgn = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), (asgn.valexp as [TypeSignature, Expression])[1], etype), (asgn.valexp as [TypeSignature, Expression])[1].sinfo, etype);

            return {keyname: asgn.keyname, valexp: [this.toTIRTypeKey(etype), easgn.expressionResult] as [TIRTypeKey, TIRExpression]};
        });

        return [env, [new TIREnvironmentFreshStatement(stmt.sinfo, assigns)]];
    }

    private checkEnvironmentSetStatement(env: StatementTypeEnvironment, stmt: EnvironmentSetStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const assigns = stmt.assigns.map<{keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}>((asgn) => {
            this.raiseErrorIf(stmt.sinfo, asgn.valexp === undefined, "cannot clear key in fresh environment creation");

            if(asgn.valexp === undefined) {
                return { keyname: asgn.keyname, valexp: undefined };
            }
            else {
                const etype = this.normalizeTypeOnly((asgn.valexp as [TypeSignature, Expression])[0], env.binds);
                const easgn = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), (asgn.valexp as [TypeSignature, Expression])[1], etype), (asgn.valexp as [TypeSignature, Expression])[1].sinfo, etype);

                return { keyname: asgn.keyname, valexp: [this.toTIRTypeKey(etype), easgn.expressionResult] as [TIRTypeKey, TIRExpression] };
            }
        });

        return [env, [new TIREnvironmentSetStatement(stmt.sinfo, assigns)]];
    }

    private checkEnvironmentSetStatementBracket(env: StatementTypeEnvironment, stmt: EnvironmentSetStatementBracket): [StatementTypeEnvironment, TIRStatement[]] {
        const assigns = stmt.assigns.map<{keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}>((asgn) => {
            this.raiseErrorIf(stmt.sinfo, asgn.valexp === undefined, "cannot clear key in fresh environment creation");

            if(asgn.valexp === undefined) {
                return { keyname: asgn.keyname, valexp: undefined };
            }
            else {
                const etype = this.normalizeTypeOnly((asgn.valexp as [TypeSignature, Expression])[0], env.binds);
                const easgn = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), (asgn.valexp as [TypeSignature, Expression])[1], etype), (asgn.valexp as [TypeSignature, Expression])[1].sinfo, etype);

                return { keyname: asgn.keyname, valexp: [this.toTIRTypeKey(etype), easgn.expressionResult] as [TIRTypeKey, TIRExpression] };
            }
        });

        const benv = this.checkScopedBlockStatement(env, stmt.block);
        return [benv[0], [new TIREnvironmentSetStatementBracket(stmt.sinfo, assigns, benv[1], stmt.isFresh)]];
    }

    private checkDeclareSingleVariableFromTaskExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vname: string, isConst: boolean, decltype: TypeSignature, infertype: ResolvedType): StatementTypeEnvironment {
        this.raiseErrorIf(sinfo, env.lookupLocalVar(vname) !== null, `${vname} cannot shadow previous definition`);

        const vtype = (decltype instanceof AutoTypeSignature) ? infertype as ResolvedType : this.normalizeTypeOnly(decltype, env.binds);
        this.raiseErrorIf(sinfo, infertype.typeID !== vtype.typeID, `expression is not of (no conversion) declared type ${vtype.typeID}`);

        return env.addVar(vname, isConst, vtype, true);
    }

    private checkAssignSingleVariableFromTaskExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vname: string, infertype: ResolvedType): StatementTypeEnvironment {
        const vinfo = env.lookupLocalVar(vname);
        this.raiseErrorIf(sinfo, vinfo === null, `Variable ${vname} was not previously defined`);
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, `Variable ${vname} is defined as const`);

        this.raiseErrorIf(sinfo, infertype.typeID !== (vinfo as VarInfo).declaredType.typeID, `expression is not of (no conversion) declared type ${(vinfo as VarInfo).declaredType.typeID}`);

        return env.setVar(vname);
    }

    private extractTaskInfo(env: StatementTypeEnvironment, ttask: TypeSignature): [ResolvedTaskAtomType, TIRTypeKey, TaskTypeDecl] {
        const rtasktry = this.normalizeTypeOnly(ttask, env.binds);
        this.raiseErrorIf(ttask.sinfo, rtasktry.options.length !== 0 || !(rtasktry.options[0] instanceof ResolvedTaskAtomType), `Expecting Task type but got ${rtasktry.typeID}`);
        const rtask = rtasktry.options[0] as ResolvedTaskAtomType;

        const tirtask = this.toTIRTypeKey(rtasktry);

        const taskdecltry = this.m_assembly.tryGetTaskTypeForFullyResolvedName(rtask.typeID);
        this.raiseErrorIf(ttask.sinfo, taskdecltry !== undefined, `Could not resolve task ${rtask.typeID}`);
        const taskdecl = taskdecltry as TaskTypeDecl;

        return [rtask, tirtask, taskdecl];
    }

    private checkTaskDeclExecArgs(sinfo: SourceInfo, env: StatementTypeEnvironment, ttask: TaskTypeDecl, tbinds: TemplateBindScope, taskargs: {argn: string, argv: Expression}[]): {argn: string, argv: TIRExpression}[] {
        const execargs = [...ttask.econtrol]
            .sort((a, b) => a.name.localeCompare(b.name))
            .map((cc) => {
                const cctype = this.normalizeTypeOnly(cc.declaredType, tbinds);
                const earg = taskargs.find((aa) => aa.argn === cc.name);
                if(earg !== undefined) {
                    return {argn: cc.name, argv: this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), earg.argv, cctype), earg.argv.sinfo, cctype).expressionResult};
                }
                else {
                    this.raiseErrorIf(sinfo, cc.defaultValue === undefined, `control property ${cc.name} requires a value but not given one at call`);

                    const lvaltry = this.reduceLiteralValueToCanonicalForm((cc.defaultValue as ConstantExpressionValue).exp, env.binds);
                    this.raiseErrorIf(sinfo, lvaltry[1].typeID !== cctype.typeID, `expected default value of type ${cctype.typeID} but got ${lvaltry[1].typeID}`);
                    this.raiseErrorIf(sinfo, lvaltry[0] === undefined, `only literal values are supported as default control values right now`);

                    return {argn: cc.name, argv: (lvaltry[0] as TIRLiteralValue).exp};
                }
            });

        return execargs;
    }

    private getTaskFieldsInitRecord(ttask: ResolvedTaskAtomType): ResolvedType {
        const tfieldsrecord = ResolvedType.createSingle(ResolvedRecordAtomType.create(ttask.task.memberFields.map((fd) => {
            return {
                pname: fd.name,
                ptype: this.normalizeTypeOnly(fd.declaredType, TemplateBindScope.createBaseBindScope(ttask.binds))
            }
        })));

        return tfieldsrecord;
    }

    private getTaskArgsTuple(ttask: ResolvedTaskAtomType): ResolvedType {
        const targstuple = ResolvedType.createSingle(ResolvedTupleAtomType.create(ttask.task.mainfunc.invoke.params.map((pp) => {
            return this.normalizeTypeOnly(pp.type, TemplateBindScope.createBaseBindScope(ttask.binds));
        })));

        return targstuple;
    }

    private checkVTargetOption(sinfo: SourceInfo, env: StatementTypeEnvironment, ttask: ResolvedTaskAtomType, isdefine: boolean, isconst: boolean, svtrgt: {name: string, vtype: TypeSignature}): [StatementTypeEnvironment, {name: string, vtype: TIRTypeKey}] {
        const rrtype = this.normalizeTypeOnly(ttask.task.mainfunc.invoke.resultType, TemplateBindScope.createBaseBindScope(ttask.binds));
        
        let eenv = env;
        if(!isdefine) {
            eenv = this.checkAssignSingleVariableFromTaskExplicit(sinfo, env, svtrgt.name, rrtype);
        }
        else {
            eenv = this.checkDeclareSingleVariableFromTaskExplicit(sinfo, env, svtrgt.name, isconst, svtrgt.vtype, rrtype);
        }
        const vtrgt = {name: svtrgt.name, vtype: this.toTIRTypeKey(rrtype)};

        return [eenv, vtrgt];
    }

    private checkVTargetOptionWithNone(sinfo: SourceInfo, env: StatementTypeEnvironment, ttask: ResolvedTaskAtomType, isdefine: boolean, isconst: boolean, svtrgt: {name: string, vtype: TypeSignature}): [StatementTypeEnvironment, {name: string, vtype: TIRTypeKey, restype: TIRTypeKey}] {
        const rrtypebase = this.normalizeTypeOnly(ttask.task.mainfunc.invoke.resultType, TemplateBindScope.createBaseBindScope(ttask.binds));
        const rrtype = this.normalizeUnionList([rrtypebase, this.getSpecialNoneType()]);

        let eenv = env;
        if(!isdefine) {
            eenv = this.checkAssignSingleVariableFromTaskExplicit(sinfo, env, svtrgt.name, rrtype);
        }
        else {
            eenv = this.checkDeclareSingleVariableFromTaskExplicit(sinfo, env, svtrgt.name, isconst, svtrgt.vtype, rrtype);
        }
        const vtrgt = {name: svtrgt.name, vtype: this.toTIRTypeKey(rrtype), restype: this.toTIRTypeKey(rrtypebase)};

        return [eenv, vtrgt];
    }

    private checkVTargetOptionWithList(sinfo: SourceInfo, env: StatementTypeEnvironment, ttask: ResolvedTaskAtomType, isdefine: boolean, isconst: boolean, svtrgt: {name: string, vtype: TypeSignature}): [StatementTypeEnvironment, {name: string, vtype: TIRTypeKey, elemtype: TIRTypeKey}] {
        const rrtypebase = this.normalizeTypeOnly(ttask.task.mainfunc.invoke.resultType, TemplateBindScope.createBaseBindScope(ttask.binds));
        const rrtype = ResolvedType.createSingle(ResolvedListEntityAtomType.create(this.m_assembly.tryGetConceptTypeForFullyResolvedName("List") as EntityTypeDecl, rrtypebase));

        let eenv = env;
        if(!isdefine) {
            eenv = this.checkAssignSingleVariableFromTaskExplicit(sinfo, env, svtrgt.name, rrtype);
        }
        else {
            eenv = this.checkDeclareSingleVariableFromTaskExplicit(sinfo, env, svtrgt.name, isconst, svtrgt.vtype, rrtype);
        }
        const vtrgt = {name: svtrgt.name, vtype: this.toTIRTypeKey(rrtype), elemtype: this.toTIRTypeKey(rrtypebase)};

        return [eenv, vtrgt];
    }

    private checkVTargetOptionWithIndex(sinfo: SourceInfo, env: StatementTypeEnvironment, ttask: ResolvedTaskAtomType, isdefine: boolean, isconst: boolean, svtrgt: {name: string, vtype: TypeSignature}): [StatementTypeEnvironment, {name: string, vtype: TIRTypeKey, restype: TIRTypeKey}] {
        const rrtypebase = this.normalizeTypeOnly(ttask.task.mainfunc.invoke.resultType, TemplateBindScope.createBaseBindScope(ttask.binds));
        const rrtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([this.getSpecialNatType(), rrtypebase]));

        let eenv = env;
        if(!isdefine) {
            eenv = this.checkAssignSingleVariableFromTaskExplicit(sinfo, env, svtrgt.name, rrtype);
        }
        else {
            eenv = this.checkDeclareSingleVariableFromTaskExplicit(sinfo, env, svtrgt.name, isconst, svtrgt.vtype, rrtype);
        }
        const vtrgt = {name: svtrgt.name, vtype: this.toTIRTypeKey(rrtype), restype: this.toTIRTypeKey(rrtypebase)};

        return [eenv, vtrgt];
    }

    private checkTaskRunStatement(env: StatementTypeEnvironment, stmt: TaskRunStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.task);
        const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

        this.raiseErrorIf(stmt.sinfo, stmt.args.length - 1 !== taskdecl.memberFields.length, `expected a field initializer + args`);

        const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
        const fieldarg = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.args[0], tfieldsrecord), stmt.sinfo, tfieldsrecord);

        this.raiseErrorIf(stmt.sinfo, stmt.args.length - 1 !== taskdecl.mainfunc.invoke.params.length, `expected ${taskdecl.mainfunc.invoke.params.length} arguments for task but got ${stmt.args.length - 1}`);
        const fargs = stmt.args.slice(1).map((arg, ii) => {
            const ptype = this.normalizeTypeOnly(taskdecl.mainfunc.invoke.params[ii].type, TemplateBindScope.createBaseBindScope(rtask.binds));
            return this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), arg, ptype), arg.sinfo, ptype).expressionResult
        });

        const [eenv, vtrgt] = this.checkVTargetOption(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgt);
        const trun = new TIRTaskRunStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgt, tirtask, execargs, {rarg: fieldarg.expressionResult, rtype: this.toTIRTypeKey(tfieldsrecord)}, fargs);
        
        return [eenv, [trun]];
    }

    private checkTaskMultiStatement(env: StatementTypeEnvironment, stmt: TaskMultiStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        let cenv = env;
        let vtrgts: {name: string, vtype: TIRTypeKey}[] = [];
        let tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[] = [];

        this.raiseErrorIf(stmt.sinfo, stmt.tasks.length !== stmt.args.length, `expected same number of tasks and argpacks but got ${stmt.tasks.length} and ${stmt.args.length}`);
        for (let i = 0; i < stmt.tasks.length; ++i) {
            const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.tasks[i]);
            const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

            const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
            const fargtuple = this.getTaskArgsTuple(rtask);
            const aargtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([tfieldsrecord, ...(fargtuple.options[0] as ResolvedTupleAtomType).types]));
            
            const argexp = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.args[i], aargtype), stmt.args[i].sinfo, aargtype);
            const [eenv, vtrgt] = this.checkVTargetOption(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgts[i]);

            cenv = eenv;
            vtrgts.push(vtrgt);
            tasks.push({task: tirtask, targs: execargs, argtype: this.toTIRTypeKey(aargtype), consargtype: this.toTIRTypeKey(tfieldsrecord), argexp: argexp.expressionResult});
        }

        const trun = new TIRTaskMultiStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgts, tasks);
        return [cenv, [trun]];
    }

    private checkTaskDashStatement(env: StatementTypeEnvironment, stmt: TaskDashStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        let cenv = env;
        let vtrgts: {name: string, vtype: TIRTypeKey, restype: TIRTypeKey}[] = [];
        let tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[] = [];

        this.raiseErrorIf(stmt.sinfo, stmt.tasks.length !== stmt.args.length, `expected same number of tasks and argpacks but got ${stmt.tasks.length} and ${stmt.args.length}`);
        for (let i = 0; i < stmt.tasks.length; ++i) {
            const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.tasks[i]);
            const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

            const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
            const fargtuple = this.getTaskArgsTuple(rtask);
            const aargtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([tfieldsrecord, ...(fargtuple.options[0] as ResolvedTupleAtomType).types]));
            
            const argexp = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.args[i], aargtype), stmt.args[i].sinfo, aargtype);
            const [eenv, vtrgt] = this.checkVTargetOptionWithNone(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgts[i]);

            cenv = eenv;
            vtrgts.push(vtrgt);
            tasks.push({task: tirtask, targs: execargs, argtype: this.toTIRTypeKey(aargtype), consargtype: this.toTIRTypeKey(tfieldsrecord), argexp: argexp.expressionResult});
        }

        const trun = new TIRTaskDashStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgts, tasks);
        return [cenv, [trun]];
    }

    private checkTaskAllStatement(env: StatementTypeEnvironment, stmt: TaskAllStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.task);
        const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

        const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
        const fargtuple = this.getTaskArgsTuple(rtask);
        const aargtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([tfieldsrecord, ...(fargtuple.options[0] as ResolvedTupleAtomType).types]));
        const aarglist = ResolvedType.createSingle(ResolvedListEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("List") as EntityTypeDecl, aargtype));

        const larg = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.arg, aarglist), stmt.arg.sinfo, aarglist);

        const [eenv, vtrgt] = this.checkVTargetOptionWithList(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgt);
        const trun = new TIRTaskAllStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgt, tirtask, execargs, larg.expressionResult, this.toTIRTypeKey(aarglist), this.toTIRTypeKey(aargtype));
        
        return [eenv, [trun]];
    }

    private checkTaskRaceStatement(env: StatementTypeEnvironment, stmt: TaskRaceStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk === "no", "This code does not permit task operations (not a task method/action)");

        const [rtask, tirtask, taskdecl] = this.extractTaskInfo(env, stmt.task);
        const execargs = this.checkTaskDeclExecArgs(stmt.sinfo, env, taskdecl, TemplateBindScope.createBaseBindScope(rtask.binds), stmt.taskargs);

        const tfieldsrecord = this.getTaskFieldsInitRecord(rtask);
        const fargtuple = this.getTaskArgsTuple(rtask);
        const aargtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([tfieldsrecord, ...(fargtuple.options[0] as ResolvedTupleAtomType).types]));
        const aarglist = ResolvedType.createSingle(ResolvedListEntityAtomType.create(this.m_assembly.tryGetObjectTypeForFullyResolvedName("List") as EntityTypeDecl, aargtype));

        const larg = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.arg, aarglist), stmt.arg.sinfo, aarglist);

        const [eenv, vtrgt] = this.checkVTargetOptionWithIndex(stmt.sinfo, env, rtask, stmt.isdefine, stmt.isconst, stmt.vtrgt);
        const trun = new TIRTaskRaceStatement(stmt.sinfo, stmt.isdefine, stmt.isconst, vtrgt, tirtask, execargs, larg.expressionResult, this.toTIRTypeKey(aarglist), this.toTIRTypeKey(aargtype));
        
        return [eenv, [trun]];
    }

    private checkTaskCallWithStatement(env: StatementTypeEnvironment, stmt: TaskCallWithStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("TaskCallWithStatement");
    }

    private checkTaskResultWithStatement(env: StatementTypeEnvironment, stmt: TaskResultWithStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("TaskResultWithStatement");
    }

    private checkTaskSetStatusStatement(env: StatementTypeEnvironment, stmt: TaskSetStatusStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("TaskSetStatusStatement");
    }

    private checkTaskSetSelfFieldStatement(env: StatementTypeEnvironment, stmt: TaskSetSelfFieldStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk !== "write", "This code does not permit task operations (not a task method/action)");
        const tsk = this.m_taskType as {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>};
        const tasktype = ResolvedType.createSingle(ResolvedTaskAtomType.create(tsk.taskdecl, tsk.taskbinds));

        const fftry = tsk.taskdecl.memberFields.find((f) => f.name === stmt.fname);
        this.raiseErrorIf(stmt.sinfo, fftry === undefined, `field ${stmt.fname} is not defined on task ${tsk.taskdecl.name}`);
        const ff = fftry as MemberFieldDecl;

        const fftype = this.normalizeTypeOnly(ff.declaredType, TemplateBindScope.createBaseBindScope(tsk.taskbinds));
        const fkey = TIRIDGenerator.generateMemberFieldID(this.toTIRTypeKey(tasktype), stmt.fname);

        const value = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.value, fftype), stmt.value.sinfo, fftype);
        const tset = new TIRTaskSetSelfFieldStatement(stmt.sinfo, this.toTIRTypeKey(tasktype), fkey, stmt.fname, value.expressionResult);

        return [env, [tset]];
    }

    private checkTaskEventEmitStatement(env: StatementTypeEnvironment, stmt: TaskEventEmitStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("TaskEventEmitStatement");
    }

    private gatherInfoTemplateTypesAndChecks(sinfo: SourceInfo, env: StatementTypeEnvironment, tt: InfoTemplate, argexps: Map<number, ResolvedType>): boolean {
        if(tt instanceof InfoTemplateConst) {
            const ccir = this.reduceLiteralValueToCanonicalForm(tt.lexp.exp, env.binds);
            return ccir[0] !== undefined;
        }
        else if (tt instanceof InfoTemplateMacro) {
            return true;
        }
        else if (tt instanceof InfoTemplateValue) {
            const oftype = this.normalizeTypeOnly(tt.argtype, env.binds);

            if(argexps.has(tt.argpos)) {
                return oftype.typeID !== (argexps.get(tt.argpos) as ResolvedType).typeID;
            }

            argexps.set(tt.argpos, oftype);
            return true;
        }
        else if (tt instanceof InfoTemplateRecord) {
            const mmok = tt.entries.map((ee) => this.gatherInfoTemplateTypesAndChecks(sinfo, env, ee.value, argexps));
            return !mmok.includes(false);
        }
        else {
            assert(tt instanceof InfoTemplateTuple);

            const mmok = (tt as InfoTemplateTuple).entries.map((ee) => this.gatherInfoTemplateTypesAndChecks(sinfo, env, ee, argexps));
            return !mmok.includes(false);
        }
    }

    private checkLoggerEmitStatement(env: StatementTypeEnvironment, stmt: LoggerEmitStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_assembly.hasNamespace(stmt.msg.namespace), `the namespace ${stmt.msg.namespace} does not exist in the application`);
        const tns = this.m_assembly.getNamespace(stmt.msg.namespace);

        this.raiseErrorIf(stmt.sinfo, !tns.msgformats.has(stmt.msg.keyname), `the namespace does not have a format named ${stmt.msg.keyname}`);
        const tt = tns.msgformats.get(stmt.msg.keyname) as InfoTemplate;

        let tmap = new Map<number, ResolvedType>();
        const ok = this.gatherInfoTemplateTypesAndChecks(stmt.sinfo, env, tt, tmap);
        this.raiseErrorIf(stmt.sinfo, !ok, "Bad format + args");

        this.raiseErrorIf(stmt.sinfo, stmt.args.length !== tmap.size, `number of expected args (${tmap.size}) and number provided (${stmt.args.length}) differ`);
        const args = stmt.args.map((arg, ii) => {
            this.raiseErrorIf(arg.sinfo, !tmap.has(ii), `Missing formatter for argument ${ii}`);
            const etype = tmap.get(ii) as ResolvedType;
            return this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), arg, etype), arg.sinfo, etype).expressionResult;
        });

        return [env, [new TIRLoggerEmitStatement(stmt.sinfo, stmt.level, stmt.msg, args)]];
    }

    private checkLoggerEmitConditionalStatement(env: StatementTypeEnvironment, stmt: LoggerEmitConditionalStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_assembly.hasNamespace(stmt.msg.namespace), `the namespace ${stmt.msg.namespace} does not exist in the application`);
        const tns = this.m_assembly.getNamespace(stmt.msg.namespace);

        this.raiseErrorIf(stmt.sinfo, !tns.msgformats.has(stmt.msg.keyname), `the namespace does not have a format named ${stmt.msg.keyname}`);
        const tt = tns.msgformats.get(stmt.msg.keyname) as InfoTemplate;

        let tmap = new Map<number, ResolvedType>();
        const ok = this.gatherInfoTemplateTypesAndChecks(stmt.sinfo, env, tt, tmap);
        this.raiseErrorIf(stmt.sinfo, !ok, "Bad format + args");

        this.raiseErrorIf(stmt.sinfo, stmt.args.length !== tmap.size, `number of expected args (${tmap.size}) and number provided (${stmt.args.length}) differ`);
        const args = stmt.args.map((arg, ii) => {
            this.raiseErrorIf(arg.sinfo, !tmap.has(ii), `Missing formatter for argument ${ii}`);
            const etype = tmap.get(ii) as ResolvedType;
            return this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), arg, etype), arg.sinfo, etype).expressionResult;
        });

        const cond = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.cond, this.getSpecialBoolType()), stmt.cond.sinfo, this.getSpecialBoolType());

        return [env, [new TIRLoggerEmitConditionalStatement(stmt.sinfo, stmt.level, cond.expressionResult, stmt.msg, args)]];
    }

    private checkLoggerLevelStatement(env: StatementTypeEnvironment, stmt: LoggerLevelStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("LoggerLevelStatement");
    }

    private checkLoggerCategoryStatement(env: StatementTypeEnvironment, stmt: LoggerCategoryStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("LoggerCategoryStatement");
    }

    private checkLoggerPrefixStatement(env: StatementTypeEnvironment, stmt: LoggerPrefixStatement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !this.m_assembly.hasNamespace(stmt.msg.namespace), `the namespace ${stmt.msg.namespace} does not exist in the application`);
        const tns = this.m_assembly.getNamespace(stmt.msg.namespace);

        this.raiseErrorIf(stmt.sinfo, !tns.msgformats.has(stmt.msg.keyname), `the namespace does not have a format named ${stmt.msg.keyname}`);
        const tt = tns.msgformats.get(stmt.msg.keyname) as InfoTemplate;

        let tmap = new Map<number, ResolvedType>();
        const ok = this.gatherInfoTemplateTypesAndChecks(stmt.sinfo, env, tt, tmap);
        this.raiseErrorIf(stmt.sinfo, !ok, "Bad format + args");

        this.raiseErrorIf(stmt.sinfo, stmt.args.length !== tmap.size, `number of expected args (${tmap.size}) and number provided (${stmt.args.length}) differ`);
        const args = stmt.args.map((arg, ii) => {
            this.raiseErrorIf(arg.sinfo, !tmap.has(ii), `Missing formatter for argument ${ii}`);
            const etype = tmap.get(ii) as ResolvedType;
            return this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), arg, etype), arg.sinfo, etype).expressionResult;
        });

        let renv = env;
        let bblock: TIRScopedBlockStatement | TIRUnscopedBlockStatement | undefined = undefined;
        if(stmt.block instanceof ScopedBlockStatement) {
            [renv, bblock] = this.checkScopedBlockStatement(env, stmt.block);
        }
        else {
            [renv, bblock] = this.checkUnscopedBlockStatement(env, stmt.block);
        }

        return [renv, [new TIRLoggerSetPrefixStatement(stmt.sinfo, stmt.msg, bblock, args)]];
    }

    private checkStatement(env: StatementTypeEnvironment, stmt: Statement): [StatementTypeEnvironment, TIRStatement[]] {
        this.raiseErrorIf(stmt.sinfo, !env.hasNormalFlow(), "Unreachable statements");

        switch(stmt.tag) {
            case StatementTag.EmptyStatement: {
                return this.checkEmptyStatement(env, stmt as EmptyStatement);
            }
            case StatementTag.VariableDeclarationStatement: {
                return this.checkVariableDeclarationStatement(env, stmt as VariableDeclarationStatement);
            }
            case StatementTag.VariableAssignmentStatement: {
                return this.checkVariableAssignStatement(env, stmt as VariableAssignmentStatement);
            }
            case StatementTag.VariableRetypeStatement: {
                return this.checkVariableRetypeStatement(env, stmt as VariableRetypeStatement);
            }
            case StatementTag.ExpressionSCReturnStatement: {
                return this.checkExpressionSCReturnStatement(env, stmt as ExpressionSCReturnStatement);
            }
            case StatementTag.VariableSCRetypeStatement: {
                return this.checkVariableSCRetypeStatement(env, stmt as VariableSCRetypeStatement);
            }
            case StatementTag.ReturnStatement: {
                return this.checkReturnStatement(env, stmt as ReturnStatement);
            }
            case StatementTag.IfElseStatement: {
                return this.checkIfStatement(env, stmt as IfStatement);
            }
            case StatementTag.SwitchStatement: {
                return this.checkSwitchStatement(env, stmt as SwitchStatement);
            }
            case StatementTag.MatchStatement: {
                return this.checkMatchStatement(env, stmt as MatchStatement);
            }
            case StatementTag.AbortStatement: {
                return this.checkAbortStatement(env, stmt as AbortStatement);
            }
            case StatementTag.AssertStatement: {
                return this.checkAssertStatement(env, stmt as AssertStatement);
            }
            case StatementTag.DebugStatement: {
                return this.checkDebugStatement(env, stmt as DebugStatement);
            }
            case StatementTag.RefCallStatement: {
                return this.checkRefCallStatement(env, stmt as RefCallStatement);
            }
            case StatementTag.EnvironmentFreshStatement: {
                return this.checkEnvironmentFreshStatement(env, stmt as EnvironmentFreshStatement);
            }
            case StatementTag.EnvironmentSetStatement: {
                return this.checkEnvironmentSetStatement(env, stmt as EnvironmentSetStatement);
            }
            case StatementTag.EnvironmentSetStatementBracket: {
                return this.checkEnvironmentSetStatementBracket(env, stmt as EnvironmentSetStatementBracket);
            }
            case StatementTag.TaskRunStatement: {
                return this.checkTaskRunStatement(env, stmt as TaskRunStatement);
            }
            case StatementTag.TaskMultiStatement: {
                return this.checkTaskMultiStatement(env, stmt as TaskMultiStatement);
            }
            case StatementTag.TaskDashStatement: {
                return this.checkTaskDashStatement(env, stmt as TaskDashStatement);
            }
            case StatementTag.TaskAllStatement: {
                return this.checkTaskAllStatement(env, stmt as TaskAllStatement);
            }
            case StatementTag.TaskRaceStatement: {
                return this.checkTaskRaceStatement(env, stmt as TaskRaceStatement);
            }
            case StatementTag.TaskCallWithStatement: {
                return this.checkTaskCallWithStatement(env, stmt as TaskCallWithStatement);
            }
            case StatementTag.TaskResultWithStatement: {
                return this.checkTaskResultWithStatement(env, stmt as TaskResultWithStatement);
            }
            case StatementTag.TaskSetStatusStatement: {
                return this.checkTaskSetStatusStatement(env, stmt as TaskSetStatusStatement);
            }
            case StatementTag.TaskSetSelfFieldStatement: {
                return this.checkTaskSetSelfFieldStatement(env, stmt as TaskSetSelfFieldStatement);
            }
            case StatementTag.TaskEventEmitStatement: {
                return this.checkTaskEventEmitStatement(env, stmt as TaskEventEmitStatement);
            }
            case StatementTag.LoggerEmitStatement: {
                return this.checkLoggerEmitStatement(env, stmt as LoggerEmitStatement);
            }
            case StatementTag.LoggerEmitConditionalStatement: {
                return this.checkLoggerEmitConditionalStatement(env, stmt as LoggerEmitConditionalStatement);
            }
            case StatementTag.LoggerLevelStatement: {
                return this.checkLoggerLevelStatement(env, stmt as LoggerLevelStatement);
            }
            case StatementTag.LoggerCategoryStatement: {
                return this.checkLoggerCategoryStatement(env, stmt as LoggerCategoryStatement);
            }
            case StatementTag.LoggerPrefixStatement: {
                return this.checkLoggerPrefixStatement(env, stmt as LoggerPrefixStatement);
            }
            default: {
                this.raiseError(stmt.sinfo, `Unknown statement kind -- ${stmt.tag}`);
                return [env, []];
            }
        }
    }

    private checkUnscopedBlockStatement(env: StatementTypeEnvironment, stmt: UnscopedBlockStatement): [StatementTypeEnvironment, TIRUnscopedBlockStatement] {
        let ops: TIRStatement[][] = [];
        let cenv = env;
        for(let i = 0; i < stmt.statements.length; ++i) {
            const [nenv, nops] = this.checkStatement(cenv, stmt.statements[i]);
            ops.push(nops);
            cenv = nenv;
        }
        this.raiseErrorIf(stmt.sinfo, !cenv.hasNormalFlow(), "unscoped blocks cannot have terminal (return/abort) operations in them");

        const flatops = ([] as TIRStatement[]).concat(...ops);
        return [cenv, new TIRUnscopedBlockStatement(flatops)];
    }

    private checkScopedBlockStatement(env: StatementTypeEnvironment, stmt: ScopedBlockStatement): [StatementTypeEnvironment, TIRScopedBlockStatement] {
        let ops: TIRStatement[][] = [];
        let cenv = env.pushLocalScope();
        for(let i = 0; i < stmt.statements.length; ++i) {
            const [nenv, nops] = this.checkStatement(cenv, stmt.statements[i]);
            ops.push(nops);
            cenv = nenv;
        }

        const flatops = ([] as TIRStatement[]).concat(...ops);
        return [cenv.popLocalScope(), new TIRScopedBlockStatement(flatops, !cenv.hasNormalFlow())];
    }

    private checkBodyExpression(srcFile: string, env: ExpressionTypeEnvironment, body: Expression, rtype: ResolvedType, selfok: "no" | "read"): TIRStatement[] {
        const evalue = this.emitCoerceIfNeeded(this.checkExpression(env, body, rtype), body.sinfo, rtype);
        const sblck = new TIRScopedBlockStatement([new TIRReturnStatement(body.sinfo, evalue.expressionResult)], true);

        return sblck.ops;
    }

    private checkBodyStatement(srcFile: string, env: StatementTypeEnvironment, body: ScopedBlockStatement, rtype: ResolvedType, taskok: boolean, selfok: "no" | "read" | "write"): TIRStatement[] {
        const sblck = this.checkScopedBlockStatement(env, body);
        return sblck[1].ops;
    }

    private processStdInvariantCheck(ttype: ResolvedType, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): TIRObjectInvariantDecl[] {
        const decltypes = this.getAllInvariantProvidingTypesInherit(ttype, tdecl, binds);
        const allfields = [...this.getAllOOFields(ttype, tdecl, binds)];

        const fargs = allfields.map((ff) => {
            return {fname: ff[1][2].name, ftype: this.normalizeTypeOnly(ff[1][2].declaredType, TemplateBindScope.createBaseBindScope(ff[1][3]))};
        });

        const chkinvsaa = decltypes.map((idp) => {
            const args = new Map<string, VarInfo>();
            fargs.forEach((ff) => {
                args.set("$" + ff.fname, new VarInfo(ff.ftype, true, true));
            });
            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgs(TemplateBindScope.createBaseBindScope(idp[2]), args);

            let invs = idp[1].invariants.filter((ie) => isBuildLevelEnabled(ie.level, this.m_buildLevel));
            return invs.map((inv) => {
                const iexp = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), inv.exp.exp, this.getSpecialBoolType()), inv.exp.exp.sinfo, this.getSpecialBoolType());
                const params = fargs.map((fa) => new TIRFunctionParameter("$" + fa.fname, this.toTIRTypeKey(fa.ftype)));

                return new TIRObjectInvariantDecl(iexp.expressionResult, params);
            });
        });
        
        return ([] as TIRObjectInvariantDecl[]).concat(...chkinvsaa);
    }

    private processStdValidateCheck(ttype: ResolvedType, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): TIRObjectValidateDecl[] {
        const decltypes = this.getAllInvariantProvidingTypesInherit(ttype, tdecl, binds);
        const allfields = [...this.getAllOOFields(ttype, tdecl, binds)];

        const fargs = allfields.map((ff) => {
            return {fname: ff[1][2].name, ftype: this.normalizeTypeOnly(ff[1][2].declaredType, TemplateBindScope.createBaseBindScope(ff[1][3]))};
        });

        const chkinvsaa = decltypes.map((idp) => {
            const args = new Map<string, VarInfo>();
            fargs.forEach((ff) => {
                args.set("$" + ff.fname, new VarInfo(ff.ftype, true, true));
            });
            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgs(TemplateBindScope.createBaseBindScope(idp[2]), args);

            let invs = idp[1].validates;
            return invs.map((inv) => {
                const iexp = this.emitCoerceIfNeeded(this.checkExpression(env, inv.exp.exp, this.getSpecialBoolType()), inv.exp.exp.sinfo, this.getSpecialBoolType());
                const params = fargs.map((fa) => new TIRFunctionParameter("$" + fa.fname, this.toTIRTypeKey(fa.ftype)));

                return new TIRObjectValidateDecl(iexp.expressionResult, params);
            });
        });
        
        return ([] as TIRObjectValidateDecl[]).concat(...chkinvsaa);
    }

    private processTypedeclInvariantsAllCheck(ttype: ResolvedType, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): TIRTypedeclInvariantDecl[] {
        const decltypes = this.getAllInvariantProvidingTypesTypedecl(ttype, tdecl, binds);

        const chkinvsaa = decltypes.map((idp) => {
            const vm = idp[1].memberMethods.find((mm) => mm.name === "value");
            const vtype = vm !== undefined ? this.normalizeTypeOnly(vm.invoke.resultType, TemplateBindScope.createBaseBindScope(idp[2])) : this.getSpecialAnyConceptType();
            const args = new Map<string, VarInfo>().set("$value", new VarInfo(vtype, true, true));
            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgs(TemplateBindScope.createBaseBindScope(idp[2]), args);

            let invs = idp[1].invariants.filter((ie) => isBuildLevelEnabled(ie.level, this.m_buildLevel));
            return invs.map((inv) => {
                const iexp = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), inv.exp.exp, this.getSpecialBoolType()), inv.exp.exp.sinfo, this.getSpecialBoolType());
                const vtype = this.toTIRTypeKey(idp[0]);

                return new TIRTypedeclInvariantDecl(iexp.expressionResult, vtype);
            });
        });
        
        return ([] as TIRTypedeclInvariantDecl[]).concat(...chkinvsaa);
    }

    private processTypedeclInvariantsConsCheck(ttype: ResolvedType, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): TIRTypedeclInvariantDecl[] {
        const vm = tdecl.memberMethods.find((mm) => mm.name === "value");
        const vtype = vm !== undefined ? this.normalizeTypeOnly(vm.invoke.resultType, TemplateBindScope.createBaseBindScope(binds)) : this.getSpecialAnyConceptType();
        const args = new Map<string, VarInfo>().set("$value", new VarInfo(vtype, true, true));
        const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgs(TemplateBindScope.createBaseBindScope(binds), args);
        
        let invs = tdecl.invariants.filter((ie) => isBuildLevelEnabled(ie.level, this.m_buildLevel));
        return invs.map((inv) => {
            const iexp = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), inv.exp.exp, this.getSpecialBoolType()), inv.exp.exp.sinfo, this.getSpecialBoolType());
            const vtype = this.toTIRTypeKey(ttype);

            return new TIRTypedeclInvariantDecl(iexp.expressionResult, vtype);
        });
    }

    private processTypedeclValidateCheck(ttype: ResolvedType, tdecl: EntityTypeDecl, binds: Map<string, ResolvedType>): TIRTypedeclValidateDecl[] {
        const decltypes = this.getAllInvariantProvidingTypesTypedecl(ttype, tdecl, binds);

        const chkinvsaa = decltypes.map((idp) => {
            const vm = idp[1].memberMethods.find((mm) => mm.name === "value");
            const vtype = vm !== undefined ? this.normalizeTypeOnly(vm.invoke.resultType, TemplateBindScope.createBaseBindScope(idp[2])) : this.getSpecialAnyConceptType();
            const args = new Map<string, VarInfo>().set("$value", new VarInfo(vtype, true, true));
            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgs(TemplateBindScope.createBaseBindScope(idp[2]), args);

            return idp[1].validates.map((inv) => {
                const iexp = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), inv.exp.exp, this.getSpecialBoolType()), inv.exp.exp.sinfo, this.getSpecialBoolType());
                const vtype = this.toTIRTypeKey(idp[0]);

                return new TIRTypedeclInvariantDecl(iexp.expressionResult, vtype);
            });
        });
        
        return ([] as TIRTypedeclInvariantDecl[]).concat(...chkinvsaa);
    }

    private processPrecondition(invk: InvokeDecl, optthistype: ResolvedType | undefined, binds: TemplateBindScope, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>, exps: PreConditionDecl[]): TIRPreConditionDecl[] {
        try {
            let fargs: TIRFunctionParameter[] = [];

            if (optthistype !== undefined) {
                fargs.push(new TIRFunctionParameter("this", this.toTIRTypeKey(optthistype)));
            }

            invk.params.forEach((ff, fname) => {
                const ptype = this.normalizeTypeGeneral(ff.type, binds);
                if (ptype instanceof ResolvedFunctionType) {
                    fargs.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
                }
                else {
                    fargs.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
                }
            });

            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgsAndPCodeArgs(binds, argpcodes, args);
            const clauses = exps
                .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
                .map((cev) => {
                    const exp = this.emitCoerceIfNeeded(this.checkExpression(env, cev.exp, this.getSpecialBoolType()), cev.exp.sinfo, this.getSpecialBoolType());

                    return new TIRPreConditionDecl(exp.expressionResult, fargs);
                });

            return clauses;
        }
        catch (ex) {
            return [];
        }
    }

    private processPostcondition(invk: InvokeDecl, optthistype: ResolvedType | undefined, binds: TemplateBindScope, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>, exps: PostConditionDecl[]): TIRPostConditionDecl[] {
        try {
            let fargs: TIRFunctionParameter[] = [];

            if (optthistype !== undefined) {
                fargs.push(new TIRFunctionParameter("this", this.toTIRTypeKey(optthistype)));
            }

            invk.params.forEach((ff, fname) => {
                const ptype = this.normalizeTypeGeneral(ff.type, binds);
                if (ptype instanceof ResolvedFunctionType) {
                    fargs.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
                }
                else {
                    fargs.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
                }
            });

            if(optthistype !== undefined && invk.isThisRef) {
                fargs.push(new TIRFunctionParameter("$this", this.toTIRTypeKey(optthistype)));
            }

            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgsAndPCodeArgs(binds, argpcodes, args);
            const clauses = exps
                .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
                .map((cev) => {
                    const exp = this.emitCoerceIfNeeded(this.checkExpression(env, cev.exp, this.getSpecialBoolType()), cev.exp.sinfo, this.getSpecialBoolType());

                    return new TIRPostConditionDecl(exp.expressionResult, fargs);
                });

            return clauses;
        }
        catch (ex) {
            return [];
        }
    }

    processOOBaseType(tkey: TIRTypeKey, rtype: ResolvedEntityAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        if (rtype instanceof ResolvedObjectEntityAtomType) {
            const tiroo = this.m_tirTypeMap.get(tkey) as TIRObjectEntityType;

            //set member fields
            tdecl.memberFields.forEach((mf) => {
                const fkey = TIRIDGenerator.generateMemberFieldID(tkey, mf.name);
                const decltype = this.toTIRTypeKey(this.normalizeTypeOnly(mf.declaredType, TemplateBindScope.createBaseBindScope(binds)));

                const tirmf = new TIRMemberFieldDecl(fkey, tkey, mf.name, mf.sourceLocation, mf.srcFile, mf.attributes, decltype);
                tiroo.memberFields.push(tirmf);
                this.m_tirFieldMap.set(fkey, tirmf);
            });

            //set all member fields
            const allf = [...this.getAllOOFields(ResolvedType.createSingle(rtype), tdecl, binds)];
            allf.forEach((ff) => {
                const enctype = this.toTIRTypeKey(ff[1][0]);
                const fkey = TIRIDGenerator.generateMemberFieldID(enctype, ff[0]);
                const ftype = this.toTIRTypeKey(this.normalizeTypeOnly(ff[1][2].declaredType, TemplateBindScope.createBaseBindScope(ff[1][3])));

                tiroo.allfields.push({ fkey: fkey, ftype: ftype });
            });

            //set invariants & validates
            const allinv = this.processStdInvariantCheck(ResolvedType.createSingle(rtype), tdecl, binds);
            tiroo.consinvariants.push(...allinv);

            const allvalidates = this.processStdValidateCheck(ResolvedType.createSingle(rtype), tdecl, binds);
            tiroo.apivalidates.push(...allvalidates);
        }
        else if (rtype instanceof ResolvedEnumEntityAtomType) {
            const tirenum = this.m_tirTypeMap.get(tkey) as TIREnumEntityType;

            //set all enum constants
            tirenum.enums.forEach((enm) => {
                const edcl = tdecl.staticMembers.find((sf) => sf.name === enm) as StaticMemberDecl;
                const decltype = this.toTIRTypeKey(this.normalizeTypeOnly(edcl.declaredType, TemplateBindScope.createBaseBindScope(binds)));
                const lvalue = this.reduceLiteralValueToCanonicalForm((edcl.value as ConstantExpressionValue).exp, TemplateBindScope.createBaseBindScope(binds));

                tirenum.litvals.set(enm, lvalue[0] as TIRLiteralValue);
                tirenum.constMembers.push(new TIRConstMemberDecl(tkey, enm, edcl.sourceLocation, edcl.srcFile, edcl.attributes, decltype, (lvalue[0] as TIRLiteralValue).exp));
            });
        }
        else if (rtype instanceof ResolvedTypedeclEntityAtomType) {
            const tirdecl = this.m_tirTypeMap.get(tkey) as TIRTypedeclEntityType;

            const allinv = this.processTypedeclInvariantsAllCheck(ResolvedType.createSingle(rtype), tdecl, binds);
            tirdecl.consinvariantsall.push(...allinv);

            const explicitinv = this.processTypedeclInvariantsConsCheck(ResolvedType.createSingle(rtype), tdecl, binds);
            tirdecl.consinvariantsexplicit.push(...explicitinv);

            const allvalidates = this.processTypedeclValidateCheck(ResolvedType.createSingle(rtype), tdecl, binds);
            tirdecl.apivalidates.push(...allvalidates);
        }
        else {
            ; //nothing else to do
        }
    }

    processOOConceptType(tkey: TIRTypeKey, rtype: ResolvedConceptAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        //nothing else to do but make sure we register the fields

        tdecl.memberFields.forEach((mf) => {
            const fkey = TIRIDGenerator.generateMemberFieldID(tkey, mf.name);
            const decltype = this.toTIRTypeKey(this.normalizeTypeOnly(mf.declaredType, TemplateBindScope.createEmptyBindScope()));

            const tirmf = new TIRMemberFieldDecl(fkey, tkey, mf.name, mf.sourceLocation, mf.srcFile, mf.attributes, decltype);
            this.m_tirFieldMap.set(fkey, tirmf);
        });

    }

    private processTaskType(tkey: TIRTypeKey, rtype: ResolvedTaskAtomType, tdecl: TaskTypeDecl) {
        const tiroo = this.m_tirTypeMap.get(tkey) as TIRTaskType;

        //set member fields
        tdecl.memberFields.forEach((mf) => {
            const fkey = TIRIDGenerator.generateMemberFieldID(tkey, mf.name);
            const decltype = this.toTIRTypeKey(this.normalizeTypeOnly(mf.declaredType, TemplateBindScope.createEmptyBindScope()));

            const tirmf = new TIRMemberFieldDecl(fkey, tkey, mf.name, mf.sourceLocation, mf.srcFile, mf.attributes, decltype);
            tiroo.memberFields.push(tirmf);
            this.m_tirFieldMap.set(fkey, tirmf);
        });

        //set controls fields
        tdecl.econtrol.forEach((mf) => {
            let litval: TIRLiteralValue | undefined = undefined;
            if(mf.defaultValue !== undefined) {
                litval = this.reduceLiteralValueToCanonicalForm(mf.defaultValue.exp, TemplateBindScope.createEmptyBindScope())[0];
                this.raiseErrorIf(mf.defaultValue.exp.sinfo, litval === undefined, `Could not resolve default value, expected a literal -- ${mf.defaultValue.exp}`);
            }

            tiroo.controls.push({val: litval, cname: mf.name});
        });

        tdecl.statuseffect.statusinfo.forEach((eff) => {
            const setype = this.normalizeTypeOnly(eff, TemplateBindScope.createEmptyBindScope());
            this.raiseErrorIf(eff.sinfo, setype.options.some((tt) => !(tt instanceof ResolvedEntityAtomType) && !(tt instanceof ResolvedConceptAtomType)), "Only nominal types can be used for status effects");

            tiroo.statuseffect.statusinfo.push(this.toTIRTypeKey(setype));
        });

        tdecl.statuseffect.statusinfo.forEach((eff) => {
            const setype = this.normalizeTypeOnly(eff, TemplateBindScope.createEmptyBindScope());
            this.raiseErrorIf(eff.sinfo, setype.options.some((tt) => !(tt instanceof ResolvedEntityAtomType) && !(tt instanceof ResolvedConceptAtomType)), "Only nominal types can be used for status effects");

            tiroo.statuseffect.statusinfo.push(this.toTIRTypeKey(setype));
        });

        if(tdecl.enveffect.evars.find((ev) => ev.vv === "*" && !ev.isw)) {
            tiroo.enveffect.readvars.push("*");
        }
        if(tdecl.enveffect.evars.find((ev) => ev.vv === "*" && ev.isw)) {
            tiroo.enveffect.writevars.push("*");
        }
        
        tdecl.enveffect.evars.forEach((eff) => {
            if(!eff.isw) {
                if(!tiroo.enveffect.readvars.includes("*") && !tiroo.enveffect.readvars.includes(eff.vv)) {
                    tiroo.enveffect.readvars.push(eff.vv);
                }
            }
            else {
                if(!tiroo.enveffect.writevars.includes("*") && !tiroo.enveffect.writevars.includes(eff.vv)) {
                    tiroo.enveffect.writevars.push(eff.vv);
                }
            }
        });

        assert(tdecl.resourceeffect.length === 0, "NOT IMPLEMENTED YET -- processTaskType");

        //mainfunc
        const dr = this.resolveMemberFunction(tdecl.sourceLocation, ResolvedType.createSingle(rtype), "main") as OOMemberLookupInfo<StaticFunctionDecl>;
        const fkey = TIRIDGenerator.generateInvokeForMemberFunction(tkey, "main", [], []);
        this.m_pendingFunctionMemberDecls.push({fkey: fkey, decl: dr, binds: new Map<string, ResolvedType>(), pcodes: new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>()});

        if(tdecl.onfuncs.onCanel !== undefined) {
            assert(false, "NOT IMPLEMENTED YET -- processTaskType");
        }

        if(tdecl.onfuncs.onFailure !== undefined) {
            assert(false, "NOT IMPLEMENTED YET -- processTaskType");
        }

        if(tdecl.onfuncs.onTimeout !== undefined) {
            assert(false, "NOT IMPLEMENTED YET -- processTaskType");
        }

        if(tdecl.lfuncs.logStart !== undefined) {
            assert(false, "NOT IMPLEMENTED YET -- processTaskType");
        }

        if(tdecl.lfuncs.logEnd !== undefined) {
            assert(false, "NOT IMPLEMENTED YET -- processTaskType");
        }

        if(tdecl.lfuncs.taskEnsures !== undefined) {
            assert(false, "NOT IMPLEMENTED YET -- processTaskType");
        }

        if(tdecl.lfuncs.taskWarns !== undefined) {
            assert(false, "NOT IMPLEMENTED YET -- processTaskType");
        }
    }

    private checkInvokeDecl(sinfo: SourceInfo, invoke: InvokeDecl) {
        const allNames = new Set<string>();
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
        }
    }

    private checkArgsAndResultTypes(sinfo: SourceInfo, args: Map<string, VarInfo>, rtype: ResolvedType) {
        this.raiseErrorIf(sinfo, rtype.isInvalidType(), "Could not resolved declared result type");

        args.forEach((vv) => {
            this.raiseErrorIf(sinfo, vv.declaredType.isInvalidType(), "Could not resolved declared argument type");
        });
    }

    private checkPCodeDecl(sinfo: SourceInfo, invoke: InvokeDecl, ibinds: TemplateBindScope) {
        const allNames = new Set<string>();
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
        
            const rtype = this.normalizeTypeGeneral(invoke.params[i].type, ibinds);
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedFunctionType, "Cannot have nested function type param");
        }
    }

    private processNamespaceFunctionInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...ibinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                tirpcodes.set(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey);
                params.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)));
        const preconds = this.processPrecondition(invoke, undefined, TemplateBindScope.createBaseBindScope(ibinds), argpcodes, fargs, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, undefined, TemplateBindScope.createBaseBindScope(ibinds), argpcodes, fargs, invoke.postconditions);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(ibinds), argpcodes, fargs);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)), false, "no");
        const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, false, false, false, false, params, false, restype, preconds, postconds, body);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processNamespaceFunctionPrimitiveInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokePrimitive {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...ibinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                tirpcodes.set(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey);
                params.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
            }
            else {
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)));
        const body = (invoke.body as BodyImplementation).body as string;
        const inv = new TIRInvokePrimitive(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, params, restype, body);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processNamespaceOperatorDeclInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl): TIRInvoke {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);
        this.raiseErrorIf(invoke.startSourceLocation, invoke.terms.length !== 0, "cannot have template parameters on operators");

        const recursive = invoke.recursive === "yes";

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeOnly(ff.type, TemplateBindScope.createEmptyBindScope());
            
            fargs.set(ff.name, new VarInfo(ptype, true, true));
            params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
        this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.length !== 0 || invoke.postconditions.length !== 0, "pre/post conditions not supported on operators yet");

        if(invoke.body === undefined) {
            const inv = new TIRInvokeAbstractDeclaration(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, new Map<string, TIRTypeKey>(), new Map<string, TIRPCodeKey>(), false, true, params, false, restype, [], []);
            
            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
        else {
            this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
            const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createEmptyBindScope(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), fargs);
            const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()), false, "no");
            const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, new Map<string, TIRTypeKey>(), new Map<string, TIRPCodeKey>(), false, false, true, false, params, false, restype, [], [], body);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
    }

    private processNamespaceOperatorImplInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);
        this.raiseErrorIf(invoke.startSourceLocation, invoke.terms.length !== 0, "cannot have template parameters on operators");

        const recursive = invoke.recursive === "yes";

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeOnly(ff.type, TemplateBindScope.createEmptyBindScope());
            fargs.set(ff.name, new VarInfo(ptype, true, true));
            params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
        this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.length !== 0 || invoke.postconditions.length !== 0, "pre/post conditions not supported on operators yet");

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createEmptyBindScope(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), fargs);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()), false, "no");
        const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, new Map<string, TIRTypeKey>(), new Map<string, TIRPCodeKey>(), false, false, true, false, params, false, restype, [], [], body);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processMemberFunctionInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...ibinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                tirpcodes.set(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey);
                params.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, undefined, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, undefined, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, invoke.postconditions);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, "no");
        const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, false, false, false, false, params, false, restype, preconds, postconds, body);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processMemberFunctionPrimitiveInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokePrimitive {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...ibinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                tirpcodes.set(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey);
                params.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
            }
            else {
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));

        const body = (invoke.body as BodyImplementation).body as string;
        const inv = new TIRInvokePrimitive(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, params, restype, body);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processMemberMethodPureDeclInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokeAbstractDeclaration {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...ibinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                tirpcodes.set(ff.name, (argpcodes.get(ff.name) as {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey);
                params.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        fargs.set("this", new VarInfo(enclosingdecl[0], true, true));

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, invoke.postconditions);

        const inv = new TIRInvokeAbstractDeclaration(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, false, params, false, restype, preconds, postconds);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processMemberMethodVirtualDeclInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...ibinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                tirpcodes.set(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey);
                params.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        fargs.set("this", new VarInfo(enclosingdecl[0], true, true));

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, invoke.postconditions);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, this.m_taskSelfOk);
        const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, true, false, false, params, false, restype, preconds, postconds, body);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processMemberMethodVirtualImplInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], declaredecl: [ResolvedType, InvokeDecl, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...ibinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                tirpcodes.set(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey);
                params.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        fargs.set("this", new VarInfo(enclosingdecl[0], true, true));

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, declaredecl[1].preconditions.length !== 0 ? declaredecl[0] : enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, declaredecl[1].preconditions.length !== 0 ? declaredecl[1].preconditions : invoke.preconditions);
        const postconds = this.processPostcondition(invoke, declaredecl[1].postconditions.length !== 0 ? declaredecl[0] : enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, declaredecl[1].postconditions.length !== 0 ? declaredecl[1].postconditions : invoke.postconditions);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, this.m_taskSelfOk);
        const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, true, false, false, params, false, restype, preconds, postconds, body);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processMemberMethodImplInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...ibinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                tirpcodes.set(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey);
                params.push(new TIRFunctionParameter(ff.name, (argpcodes.get(ff.name) as {pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        fargs.set("this", new VarInfo(enclosingdecl[0], !invoke.isThisRef, true));
        
        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs, invoke.postconditions);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), this.m_taskOpsOk, this.m_taskSelfOk);
        const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, false, false, false, params, invoke.isThisRef, restype, preconds, postconds, body);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processPCodeInvokeInfo(codepack: TIRCodePack, invoke: InvokeDecl, desiredfunc: ResolvedFunctionType, declbinds: TemplateBindScope, bodybinds: Map<string, ResolvedType>, capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, capturedvars: Map<string, {vname: string, vtype: ResolvedType}>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvokeImplementation {
        this.checkPCodeDecl(invoke.startSourceLocation, invoke, declbinds);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...argpcodes].some((pc) => pc[1].pcode.recursive));

        const tbinds = new Map<string, TIRTypeKey>();
        [...bodybinds].forEach((bb) => {
            tbinds.set(bb[0], this.toTIRTypeKey(bb[1]));
        });

        let cvars = new Map<string, VarInfo>();
        capturedvars.forEach((cv) => cvars.set(cv.vname, new VarInfo(cv.vtype, true, true)));

        let tirpcodes = new Map<string, TIRPCodeKey>();
        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff, ii) => {
            const ptype = desiredfunc.params[ii].type as ResolvedType;
           
            fargs.set(ff.name, new VarInfo(ptype, true, true));
            params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
        });

        const restype = this.toTIRTypeKey(desiredfunc.resultType);

        let body: TIRStatement[] = [];
        let bimpl = (invoke.body as BodyImplementation).body;
        if(bimpl instanceof Expression) {
            const env = ExpressionTypeEnvironment.createInitialEnvForExpressionEval(TemplateBindScope.createBaseBindScope(bodybinds), capturedpcodes, cvars, argpcodes, fargs, []);
            body = this.checkBodyExpression(invoke.srcFile, env, bimpl, desiredfunc.resultType, "no");
        }
        else {
            const env = StatementTypeEnvironment.createInitialEnvForStatementEval(TemplateBindScope.createBaseBindScope(bodybinds), capturedpcodes, cvars, argpcodes, fargs, []);
            body = this.checkBodyStatement(invoke.srcFile, env, bimpl as ScopedBlockStatement, desiredfunc.resultType, false, "no");
        }

        const inv = new TIRInvokeImplementation(codepack.invk, "lambda", invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, false, false, false, true, params, false, restype, [], [], body);

        this.m_tirInvokeMap.set(codepack.invk, inv);
        return inv;
    }

    private ensureTIRNamespaceDecl(ns: string): TIRNamespaceDeclaration {
        if(!this.m_tirNamespaceMap.has(ns)) {
            this.m_tirNamespaceMap.set(ns, new TIRNamespaceDeclaration(ns));
        }

        return this.m_tirNamespaceMap.get(ns) as TIRNamespaceDeclaration;
    }

    private ensureTIRTypeDecl(ns: string, tkey: TIRTypeKey): [TIRNamespaceDeclaration, TIROOType] {
        const nsi = this.ensureTIRNamespaceDecl(ns);
        assert(this.m_tirTypeMap.has(tkey), `Should always process types before any members -- ${tkey}`);

        return [nsi, this.m_tirTypeMap.get(tkey) as TIROOType]
    }

    private processConstExpr(cdcl: NamespaceConstDecl) {
        const tirns = this.ensureTIRNamespaceDecl(cdcl.ns);
        if(tirns.consts.has(cdcl.name)) {
            return;
        }

        try {
            this.m_file = cdcl.srcFile;
            this.m_ns = cdcl.ns;
            this.m_rtype = this.getSpecialNoneType();
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            const decltype = this.normalizeTypeOnly(cdcl.declaredType, TemplateBindScope.createEmptyBindScope());
            const tirdecltype = this.toTIRTypeKey(decltype);

            this.raiseErrorIf(cdcl.value.exp.sinfo, cdcl.value.captured.size !== 0, "cannot have unbound variables in namespace const expression");
            const declvalue = this.emitCoerceIfNeeded(this.checkExpression(ExpressionTypeEnvironment.createInitialEnvForEvalStandalone(TemplateBindScope.createEmptyBindScope()), cdcl.value.exp, decltype), cdcl.value.exp.sinfo, decltype);

            const tridecl = new TIRNamespaceConstDecl(cdcl.ns, cdcl.name, cdcl.sourceLocation, cdcl.srcFile, cdcl.attributes, tirdecltype, declvalue.expressionResult);
            tirns.consts.set(cdcl.name, tridecl);
        }
        catch (ex) {
            ;
        }
    }

    private processNamespaceFunctionDecl(fkey: TIRInvokeKey, ns: string, name: string, invoke: InvokeDecl, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>) {
        const tirns = this.ensureTIRNamespaceDecl(ns);
        if(tirns.functions.has(name) && (tirns.functions.get(name) as TIRNamespaceFunctionDecl[]).find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        try {
            this.m_file = invoke.srcFile;
            this.m_ns = ns;
            this.m_rtype = this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(binds));
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            let iinv: TIRInvoke | undefined = undefined;
            if(typeof((invoke.body as BodyImplementation).body) === "string") {
                iinv = this.processNamespaceFunctionPrimitiveInvokeInfo(name, fkey, invoke, binds, pcodes);
            }
            else {
                iinv = this.processNamespaceFunctionInvokeInfo(name, fkey, invoke, binds, pcodes);
            }

            if(!tirns.functions.has(name)) {
                tirns.functions.set(name, []);
            }
            (tirns.functions.get(name) as TIRNamespaceFunctionDecl[]).push(new TIRNamespaceFunctionDecl(ns, invoke.startSourceLocation, invoke.srcFile, iinv));
        }
        catch (ex) {
           ;
        }
    }

    private processNamespaceOperatorDecl(fkey: TIRInvokeKey, ns: string, name: string, invoke: InvokeDecl) {
        const tirns = this.ensureTIRNamespaceDecl(ns);
        if(tirns.operators.has(name) && (tirns.operators.get(name) as TIRNamespaceOperatorDecl[]).find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        try {
            this.m_file = invoke.srcFile;
            this.m_ns = ns;
            this.m_rtype = this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope());
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            const iinv = this.processNamespaceOperatorDeclInvokeInfo(name, fkey, invoke);

            const tirns = this.ensureTIRNamespaceDecl(ns);
            if(!tirns.operators.has(name)) {
                tirns.operators.set(name, []);
            }
            (tirns.operators.get(name) as TIRNamespaceOperatorDecl[]).push(new TIRNamespaceOperatorDecl(ns, invoke.startSourceLocation, invoke.srcFile, iinv));
        }
        catch (ex) {
           ;
        }
    }

    private processNamespaceOperatorImpl(fkey: TIRInvokeKey, ns: string, name: string, invoke: InvokeDecl) {
        const tirns = this.ensureTIRNamespaceDecl(ns);
        if(tirns.operators.has(name) && (tirns.operators.get(name) as TIRNamespaceOperatorDecl[]).find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        try {
            this.m_file = invoke.srcFile;
            this.m_ns = ns;
            this.m_rtype = this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope());
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            const iinv = this.processNamespaceOperatorImplInvokeInfo(name, fkey, invoke);

            if(!tirns.operators.has(name)) {
                tirns.operators.set(name, []);
            }
            (tirns.operators.get(name) as TIRNamespaceOperatorDecl[]).push(new TIRNamespaceOperatorDecl(ns, invoke.startSourceLocation, invoke.srcFile, iinv));
        }
        catch (ex) {
           ;
        }
    }

    private processLambdaFunction(cpdata: TIRCodePack, cpdecl: InvokeDecl, desiredfunc: ResolvedFunctionType, declbinds: TemplateBindScope, bodybinds: Map<string, ResolvedType>, capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, capturedvars: Map<string, {vname: string, vtype: ResolvedType}>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>) {
        const tirns = this.ensureTIRNamespaceDecl(cpdecl.namespace);
        if(tirns.lambdas.has(cpdata.invk)) {
            return;
        }

        try {
            this.m_file = cpdecl.srcFile;
            this.m_ns = cpdecl.namespace;
            this.m_rtype = desiredfunc.resultType;
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            const iinv = this.processPCodeInvokeInfo(cpdata, cpdecl, desiredfunc, declbinds, bodybinds, capturedpcodes, capturedvars, argpcodes);

            tirns.lambdas.set(cpdata.invk, new TIRNamespaceLambdaDecl(cpdata.codekey, cpdecl.startSourceLocation, cpdecl.srcFile, iinv));
            tirns.codepacks.set(cpdata.codekey, cpdata);

            this.m_tirCodePackMap.set(cpdata.codekey, cpdata);
        }
        catch (ex) {
           ;
        }
    }

    private processMemberConst(decl: [ResolvedType, OOPTypeDecl, StaticMemberDecl, Map<string, ResolvedType>]) {
        const [_, tirtt] = this.ensureTIRTypeDecl(decl[1].ns, decl[0].typeID);
        
        if(tirtt.constMembers.find((tdcl) => tdcl.name === decl[2].name) !== undefined) {
            return;
        }

        try {
            this.m_file = decl[2].srcFile;
            this.m_ns = decl[1].ns;
            this.m_rtype = this.normalizeTypeOnly(decl[2].declaredType, TemplateBindScope.createBaseBindScope(decl[3]));
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            const decltype = this.normalizeTypeOnly(decl[2].declaredType, TemplateBindScope.createBaseBindScope(decl[3]));
            const tirdecltype = this.toTIRTypeKey(decltype);

            this.raiseErrorIf(decl[2].value.exp.sinfo, decl[2].value.captured.size !== 0, "cannot have unbound variables in namespace const expression");
            const declvalue = this.emitCoerceIfNeeded(this.checkExpression(ExpressionTypeEnvironment.createInitialEnvForEvalStandalone(TemplateBindScope.createBaseBindScope(decl[3])), decl[2].value.exp, decltype), decl[2].value.exp.sinfo, decltype);

            tirtt.constMembers.push(new TIRConstMemberDecl(tirtt.tkey, decl[2].name, decl[2].sourceLocation, decl[2].srcFile, decl[2].attributes, tirdecltype, declvalue.expressionResult));
        }
        catch(ex) {
            ;
        }
    }

    private processMemberFunction(fkey: TIRInvokeKey, decl: OOMemberLookupInfo<StaticFunctionDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>) {
        const [_, tirtt] = this.ensureTIRTypeDecl(decl.ootype.ns, decl.ttype.typeID);
        
        if(tirtt.staticFunctions.find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        try {
            this.m_file = decl.decl.srcFile;
            this.m_ns = decl.ootype.ns;
            this.m_rtype = this.normalizeTypeOnly(decl.decl.invoke.resultType, TemplateBindScope.createBaseBindScope(decl.oobinds).pushScope(binds));
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            const tirinv = typeof((decl.decl.invoke.body as BodyImplementation).body) === "string" ? this.processMemberFunctionPrimitiveInvokeInfo(decl.decl.name, fkey, decl.decl.invoke, [decl.ttype, decl.ootype, decl.oobinds], binds, pcodes) : this.processMemberFunctionInvokeInfo(decl.decl.name, fkey, decl.decl.invoke, [decl.ttype, decl.ootype, decl.oobinds], binds, pcodes);
            tirtt.staticFunctions.push(new TIRStaticFunctionDecl(tirtt.tkey, decl.decl.sourceLocation, decl.decl.srcFile, tirinv));   
        }
        catch(ex) {
            ;
        }
    }

    private processMemberMethodVirtual(fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, virtualmemberdecls: {fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>}[]) {
        const [_, tirtt] = this.ensureTIRTypeDecl(decl.ootype.ns, decl.ttype.typeID);
        
        if(tirtt.memberMethods.find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        virtualmemberdecls.push({fkey: fkey, decl: decl, binds: binds, pcodes: pcodes});
        try {
            this.m_file = decl.decl.srcFile;
            this.m_ns = decl.ootype.ns;
            this.m_rtype = this.normalizeTypeOnly(decl.decl.invoke.resultType, TemplateBindScope.createBaseBindScope(decl.oobinds).pushScope(binds));
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            const tirinv = decl.decl.invoke.body === undefined ? this.processMemberMethodPureDeclInvokeInfo(decl.decl.name, fkey, decl.decl.invoke, [decl.ttype, decl.ootype, decl.oobinds], binds, pcodes) : this.processMemberMethodVirtualDeclInvokeInfo(decl.decl.name, fkey, decl.decl.invoke, [decl.ttype, decl.ootype, decl.oobinds], binds, pcodes);
            tirtt.memberMethods.push(new TIRMemberMethodDecl(tirtt.tkey, decl.decl.sourceLocation, decl.decl.srcFile, tirinv));   
        }
        catch(ex) {
            ;
        }
    }

    private processMemberMethodOverride(fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, declaredecl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>) {
        const [_, tirtt] = this.ensureTIRTypeDecl(decl.ootype.ns, decl.ttype.typeID);
        
        if(tirtt.memberMethods.find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        try {
            this.m_file = decl.decl.srcFile;
            this.m_rtype = this.normalizeTypeOnly(decl.decl.invoke.resultType, TemplateBindScope.createBaseBindScope(decl.oobinds).pushScope(binds));
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            const tirinv = this.processMemberMethodVirtualImplInvokeInfo(decl.decl.name, fkey, decl.decl.invoke, [decl.ttype, decl.ootype, decl.oobinds], [declaredecl.ttype, declaredecl.decl.invoke, declaredecl.ootype, declaredecl.oobinds], binds, pcodes);
            tirtt.memberMethods.push(new TIRMemberMethodDecl(tirtt.tkey, decl.decl.sourceLocation, decl.decl.srcFile, tirinv));   
        }
        catch(ex) {
            ;
        }
    }

    private processMemberMethodDirect(fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>) {
        const [_, tirtt] = this.ensureTIRTypeDecl(decl.ootype.ns, decl.ttype.typeID);
        
        if(tirtt.memberMethods.find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        try {
            this.m_file = decl.decl.srcFile;
            this.m_ns = decl.ootype.ns;
            this.m_rtype = this.normalizeTypeOnly(decl.decl.invoke.resultType, TemplateBindScope.createBaseBindScope(decl.oobinds).pushScope(binds));
            if(!decl.decl.invoke.isThisRef) {
                this.m_returnMode = ReturnMode.Standard;
            }
            else {
                this.m_returnMode = (decl.ootype instanceof TaskTypeDecl) ? ReturnMode.MemberSelf : ReturnMode.MemberRef;
            }

            this.m_taskOpsOk = decl.ootype instanceof TaskTypeDecl;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;
            this.m_scratchCtr = 0;

            if(this.m_taskOpsOk) {
                this.m_taskType = {taskdecl: decl.ootype as TaskTypeDecl, taskbinds: binds};
                this.m_taskSelfOk = (decl.decl.invoke.isThisRef) ? "write" : "read";
            }

            const tirinv = this.processMemberMethodImplInvokeInfo(decl.decl.name, fkey, decl.decl.invoke, [decl.ttype, decl.ootype, decl.oobinds], binds, pcodes);
            tirtt.memberMethods.push(new TIRMemberMethodDecl(tirtt.tkey, decl.decl.sourceLocation, decl.decl.srcFile, tirinv));   
        }
        catch(ex) {
            ;
        }
    }

    private processMemberTaskAction(fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>) {
        const [_, tirtt] = this.ensureTIRTypeDecl(decl.ootype.ns, decl.ttype.typeID);
        
        if(tirtt.memberMethods.find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        try {
            this.m_file = decl.decl.srcFile;
            this.m_ns = decl.ootype.ns;
            this.m_rtype = this.normalizeTypeOnly(decl.decl.invoke.resultType, TemplateBindScope.createBaseBindScope(decl.oobinds).pushScope(binds));
            this.m_returnMode = ReturnMode.MemberAction;
            this.m_taskOpsOk = true;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;

            if(this.m_taskOpsOk) {
                this.m_taskType = {taskdecl: decl.ootype as TaskTypeDecl, taskbinds: binds};
                this.m_taskSelfOk = (decl.decl.invoke.isThisRef) ? "write" : "read";
            }

            const tirinv = this.processMemberMethodImplInvokeInfo(decl.decl.name, fkey, decl.decl.invoke, [decl.ttype, decl.ootype, decl.oobinds], binds, pcodes);
            tirtt.memberMethods.push(new TIRMemberMethodDecl(tirtt.tkey, decl.decl.sourceLocation, decl.decl.srcFile, tirinv));   
        }
        catch(ex) {
            ;
        }
    }

    private processMemberTaskMain(fkey: TIRInvokeKey, decl: OOMemberLookupInfo<StaticFunctionDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>) {
        const [_, tirtt] = this.ensureTIRTypeDecl(decl.ootype.ns, decl.ttype.typeID);
        
        if(tirtt.staticFunctions.find((tdcl) => tdcl.ikey === fkey) !== undefined) {
            return;
        }

        try {
            this.m_file = decl.decl.srcFile;
            this.m_ns = decl.ootype.ns;
            this.m_rtype = this.normalizeTypeOnly(decl.decl.invoke.resultType, TemplateBindScope.createBaseBindScope(decl.oobinds).pushScope(binds));
            this.m_returnMode = ReturnMode.Standard;
            this.m_taskOpsOk = true;
            this.m_taskSelfOk = "write";
            this.m_taskType = {taskdecl: decl.ootype as TaskTypeDecl, taskbinds: binds};
            this.m_scratchCtr = 0;

            const tirinv = this.processMemberFunctionInvokeInfo(decl.decl.name, fkey, decl.decl.invoke, [decl.ttype, decl.ootype, decl.oobinds], binds, pcodes);
            tirtt.staticFunctions.push(new TIRMemberMethodDecl(tirtt.tkey, decl.decl.sourceLocation, decl.decl.srcFile, tirinv));   
        }
        catch(ex) {
            ;
        }
    }

    private processRegexAndValidatorInfo(): {literalre: BSQRegex[], validatorsre: Map<TIRTypeKey, BSQRegex>, pathvalidators: Map<TIRTypeKey, PathValidator>} {
        const vre = new Map<TIRTypeKey, BSQRegex>();
         [...this.m_assembly.m_validatorRegexs].forEach((rr) => {
            vre.set(rr[0], rr[1]);
        });

        const vpth = new Map<TIRTypeKey, PathValidator>();
        [...this.m_assembly.m_validatorPaths].forEach((vp) => {
            vpth.set(vp[0], vp[1]);
        });

        return { literalre: this.m_assembly.m_literalRegexs, validatorsre: vre, pathvalidators: vpth };
    }

    private anyTypesPending(): boolean {
        return this.m_pendingEntityDecls.length !== 0 ||
            this.m_pendingEnumDecls.length !== 0 ||
            this.m_pendingTypedeclDecls.length !== 0 ||
            this.m_pendingConceptDecls.length !== 0 ||
            this.m_pendingTaskDecls.length !== 0;
    }
    
    private anyPending(): boolean {
        if(this.anyTypesPending()) {
            return true;
        }

        return this.m_pendingNamespaceConsts.length !== 0 ||
            this.m_pendingNamespaceFunctions.length !== 0 ||
            this.m_pendingNamespaceOperators.length !== 0 ||
            this.m_pendingConstMemberDecls.length !== 0 ||
            this.m_pendingFunctionMemberDecls.length !== 0 ||
            this.m_pendingMethodMemberDecls.length !== 0 ||
            this.m_pendingCodeDecls.length !== 0;
    }

    private updateVirtualPending(virtualmemberdecls: {fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>}[]) {
        for(let i = 0; i < virtualmemberdecls.length; ++i) {
            const vmd = virtualmemberdecls[i];

            for(let j = 0; j < this.m_instantiatedVTableTypes.length; ++j) {
                const vtt = this.m_instantiatedVTableTypes[j];
                const tirvtt = this.m_tirTypeMap.get(vtt.typeID) as TIRObjectEntityType;

                if(this.subtypeOf(ResolvedType.createSingle(vtt), vmd.decl.ttype) && !tirvtt.vtable.has(vmd.decl.decl.name)) {
                    const mresolvetry = this.resolveMemberMethod(vtt.object.sourceLocation, ResolvedType.createSingle(vtt), vmd.decl.decl.name);
                    this.raiseErrorIf(vtt.object.sourceLocation, mresolvetry === undefined, `Could not resolve method name "${vmd.decl.decl.name}" from type ${vtt.typeID}`);
                    const mresolve = mresolvetry as OOMemberResolution<MemberMethodDecl>;

                    this.raiseErrorIf(vtt.object.sourceLocation, mresolve.impl.length !== 1, `Could not resolve implementation for non-virtual method ${vmd.decl.decl.name} from ${vtt.typeID}`);
                    const knownimpl = mresolve.impl[0];

                    const knowntype = this.toTIRTypeKey(knownimpl.ttype);
                    const ptypes = vmd.decl.decl.invoke.params.map((pp) => {
                        const rptype = this.normalizeTypeGeneral(pp.type, TemplateBindScope.createBaseBindScope(vmd.decl.oobinds).pushScope(vmd.binds));
                        return {name: pp.name, rptype: rptype};
                    });

                    const knownkey = TIRIDGenerator.generateInvokeForMemberMethod(knowntype, vmd.decl.decl.name, knownimpl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(vmd.binds.get(tt.name) as ResolvedType)), ptypes.filter((pp) => pp.rptype instanceof ResolvedFunctionType).map((pp) => (vmd.pcodes.get(pp.name) as {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}).pcode.codekey));
                
                    this.m_pendingMethodMemberDecls.push({fkey: knownkey, decl: knownimpl, declaredecl: mresolve.decl, binds: vmd.binds, pcodes: vmd.pcodes});
                    tirvtt.vtable.set(vmd.decl.decl.name, knownkey);
                }
            }
        }
    }

    private processInfoTemplate(msg: InfoTemplate): TIRInfoTemplate {
        if (msg instanceof InfoTemplateRecord) {
            const entries = msg.entries.map((ee) => {
                return {name: ee.name, value: this.processInfoTemplate(ee.value)};
            });
            return new TIRInfoTemplateRecord(entries);
        }
        else if (msg instanceof InfoTemplateTuple) {
            const entries = msg.entries.map((ee) => {
                return this.processInfoTemplate(ee);
            });
            return new TIRInfoTemplateTuple(entries);
        }
        else if (msg instanceof InfoTemplateConst) {
            const [tirlit, _] = this.reduceLiteralValueToCanonicalForm(msg.lexp.exp, TemplateBindScope.createEmptyBindScope());
            this.raiseErrorIf(msg.lexp.exp.sinfo, tirlit === undefined, `expected literal expression but got ${msg.lexp.exp}`);

            return new TIRInfoTemplateConst(tirlit as TIRLiteralValue);
        }
        else if (msg instanceof InfoTemplateMacro) {
            return new TIRInfoTemplateMacro(msg.macro);
        }
        else {
            assert(msg instanceof InfoTemplateValue, `Unknown info template kind ${msg}`);

            const vmsg = msg as InfoTemplateValue;
            return new TIRInfoTemplateValue(vmsg.argpos, this.toTIRTypeKey(this.normalizeTypeOnly(vmsg.argtype, TemplateBindScope.createEmptyBindScope())));
        }
    }

    private processSpecialTypes() {
        this.toTIRTypeKey(this.getSpecialNoneType());
        this.toTIRTypeKey(this.getSpecialBoolType());
        this.toTIRTypeKey(this.getSpecialIntType());
        this.toTIRTypeKey(this.getSpecialNatType());
        this.toTIRTypeKey(this.getSpecialBigIntType());
        this.toTIRTypeKey(this.getSpecialBigNatType());
        this.toTIRTypeKey(this.getSpecialRationalType());
        this.toTIRTypeKey(this.getSpecialFloatType());
        this.toTIRTypeKey(this.getSpecialDecimalType());
        this.toTIRTypeKey(this.getSpecialStringType());
        this.toTIRTypeKey(this.getSpecialASCIIStringType());
        this.toTIRTypeKey(this.getSpecialByteBufferType());
        this.toTIRTypeKey(this.getSpecialDateTimeType());
        this.toTIRTypeKey(this.getSpecialUTCDateTimeType());
        this.toTIRTypeKey(this.getSpecialPlainDateType());
        this.toTIRTypeKey(this.getSpecialPlainTimeType());

        this.toTIRTypeKey(this.getSpecialTickTimeType());
        this.toTIRTypeKey(this.getSpecialLogicalTimeType());
        this.toTIRTypeKey(this.getSpecialISOTimeStampType());
        this.toTIRTypeKey(this.getSpecialUUID4Type());
        this.toTIRTypeKey(this.getSpecialUUID7Type());
        this.toTIRTypeKey(this.getSpecialSHAContentHashType());
        this.toTIRTypeKey(this.getSpecialLatLongCoordinateType());
        this.toTIRTypeKey(this.getSpecialRegexType());
        this.toTIRTypeKey(this.getSpecialNothingType());
        this.toTIRTypeKey(this.getSpecialTaskIDType());

        this.toTIRTypeKey(this.getSpecialAnyConceptType());
        this.toTIRTypeKey(this.getSpecialSomeConceptType());

        this.toTIRTypeKey(this.getSpecialKeyTypeConceptType());
        this.toTIRTypeKey(this.getSpecialValidatorConceptType());
        this.toTIRTypeKey(this.getSpecialPathValidatorConceptType());

        this.toTIRTypeKey(this.getSpecialTestableTypeConceptType());
        this.toTIRTypeKey(this.getSpecialAPITypeConceptType());
        this.toTIRTypeKey(this.getSpecialTupleConceptType());
        this.toTIRTypeKey(this.getSpecialRecordConceptType());

        this.toTIRTypeKey(this.getSpecialISomethingConceptType());
        this.toTIRTypeKey(this.getSpecialIOptionConceptType());
        this.toTIRTypeKey(this.getSpecialIOptionTConceptType());

        this.toTIRTypeKey(this.getSpecialIResultConceptType());
        this.toTIRTypeKey(this.getSpecialIOkConceptType());
        this.toTIRTypeKey(this.getSpecialIErrTConceptType());
        this.toTIRTypeKey(this.getSpecialIResultTConceptType());
        this.toTIRTypeKey(this.getSpecialIResultEConceptType());

        this.toTIRTypeKey(this.getSpecialObjectConceptType());

        if (this.m_issmtbuild) {
            this.toTIRTypeKey(this.getSpecialHavocType());
        }
    }

    static processAssembly(asm: Assembly, buildlevel: BuildLevel, istestbuild: boolean, isoverflowfailure: boolean, issmtbuild: boolean, exportvals: {ns: string, fname: string}[]): { tasm: TIRAssembly | undefined, errors: string[] } {
        let tchecker = new TypeChecker(asm, buildlevel, isoverflowfailure, issmtbuild, istestbuild);

        //Must always have Core namespace and special types registered -- even if just as default values
        tchecker.m_tirNamespaceMap.set("Core", new TIRNamespaceDeclaration("Core"));
        tchecker.processSpecialTypes();

        exportvals.forEach((ee) => {
            //could be function, const, task, or type
            const nsdecl = asm.getNamespace(ee.ns);

            if(nsdecl.functions.has(ee.fname)) {
                const fdecl = nsdecl.functions.get(ee.fname) as NamespaceFunctionDecl;
                tchecker.raiseErrorIf(fdecl.invoke.startSourceLocation, fdecl.invoke.terms.length !== 0 || fdecl.invoke.params.some((pp) => pp.type instanceof FunctionTypeSignature), "Exported functions cannot have template params or lambdas");

                const fkey = TIRIDGenerator.generateInvokeIDForNamespaceFunction(nsdecl.ns, ee.fname, [], []);
                tchecker.m_pendingNamespaceFunctions.push({fkey: fkey, decl: fdecl, binds: new Map<string, ResolvedType>(), pcodes: new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>()});
            }
            else {
                assert(false, "export of non functions is not supported yet");
            }
        });

        let virtualmemberdecls: {fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>}[] = [];

        //process info decls
        let infoformats = new Map<string, TIRInfoTemplate>();
        let stemplates = new Map<string, TIRStringTemplate>();
        asm.getNamespaces().forEach((nsd) => {
            nsd.msgformats.forEach((mfmt, name) => {
                infoformats.set(name, tchecker.processInfoTemplate(mfmt));
            });

            nsd.stringformats.forEach((sfmt, name) => {
                stemplates.set(name, new TIRStringTemplate(sfmt.str));
            });
        });

        while(tchecker.anyPending()) {
            while(tchecker.anyTypesPending()) {
                if(tchecker.m_pendingEntityDecls.length !== 0) {
                    const edecl = tchecker.m_pendingEntityDecls.shift() as {tirtype: TIRObjectEntityType, rtype: ResolvedEntityAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>};
                    tchecker.processOOBaseType(edecl.tirtype.tkey, edecl.rtype, edecl.tdecl, edecl.binds);
                }
                else if(tchecker.m_pendingEnumDecls.length !== 0) {
                    const edecl = tchecker.m_pendingEnumDecls.shift() as {tirtype: TIREnumEntityType, rtype: ResolvedEnumEntityAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>};
                    tchecker.processOOBaseType(edecl.tirtype.tkey, edecl.rtype, edecl.tdecl, edecl.binds);
                }
                else if(tchecker.m_pendingTypedeclDecls.length !== 0) {
                    const edecl = tchecker.m_pendingTypedeclDecls.shift() as {tirtype: TIRTypedeclEntityType, rtype: ResolvedTypedeclEntityAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>};
                    tchecker.processOOBaseType(edecl.tirtype.tkey, edecl.rtype, edecl.tdecl, edecl.binds);
                }
                else if(tchecker.m_pendingConceptDecls.length !== 0) {
                    const cdecl = tchecker.m_pendingConceptDecls.shift() as {tirtype: TIRConceptType, rtype: ResolvedConceptAtomTypeEntry, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>};
                    tchecker.processOOConceptType(cdecl.tirtype.tkey, ResolvedConceptAtomType.create([cdecl.rtype]), cdecl.tdecl, cdecl.binds);
                }
                else {
                    const tdecl = tchecker.m_pendingTaskDecls.shift() as {tirtype: TIRTaskType, rtype: ResolvedTaskAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>};
                    tchecker.processTaskType(tdecl.tirtype.tkey, tdecl.rtype, tdecl.tdecl as TaskTypeDecl);
                }
            }

            if(tchecker.m_pendingNamespaceConsts.length !== 0) {
                const cdecl = tchecker.m_pendingNamespaceConsts.shift() as NamespaceConstDecl;
                tchecker.processConstExpr(cdecl);
            }
            else if(tchecker.m_pendingNamespaceFunctions.length !== 0) {
                const nfd = tchecker.m_pendingNamespaceFunctions.shift() as {fkey: TIRInvokeKey, decl: NamespaceFunctionDecl, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>};
                tchecker.processNamespaceFunctionDecl(nfd.fkey, nfd.decl.ns, nfd.decl.name, nfd.decl.invoke, nfd.binds, nfd.pcodes);
            }
            else if(tchecker.m_pendingNamespaceOperators.length !== 0) {
                const nfd = tchecker.m_pendingNamespaceOperators.shift() as {fkey: TIRInvokeKey, decl: NamespaceOperatorDecl, impls: {fkey: TIRInvokeKey, decl: NamespaceOperatorDecl}[]};
                tchecker.processNamespaceOperatorDecl(nfd.fkey, nfd.decl.ns, nfd.decl.name, nfd.decl.invoke);

                nfd.impls.forEach((ff) => {
                    tchecker.processNamespaceOperatorImpl(ff.fkey, ff.decl.ns, ff.decl.name, ff.decl.invoke);
                });
            }
            else if(tchecker.m_pendingConstMemberDecls.length !== 0) {
                const mcc = tchecker.m_pendingConstMemberDecls.shift() as OOMemberLookupInfo<StaticMemberDecl>;
                tchecker.processMemberConst([mcc.ttype, mcc.ootype, mcc.decl, mcc.oobinds]);
            }
            else if(tchecker.m_pendingFunctionMemberDecls.length !== 0) {
                const mfd = tchecker.m_pendingFunctionMemberDecls.shift() as {fkey: TIRInvokeKey, decl: OOMemberLookupInfo<StaticFunctionDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>};
                if(mfd.decl.ootype instanceof TaskTypeDecl && mfd.decl.decl.name === "main") {
                    tchecker.processMemberTaskMain(mfd.fkey, mfd.decl, mfd.binds, mfd.pcodes);
                }
                else {
                    tchecker.processMemberFunction(mfd.fkey, mfd.decl, mfd.binds, mfd.pcodes);
                }
            }
            else if(tchecker.m_pendingMethodMemberDecls.length !== 0) {
                const mmd = tchecker.m_pendingMethodMemberDecls.shift() as {fkey: TIRInvokeKey, decl: OOMemberLookupInfo<MemberMethodDecl>, declaredecl: OOMemberLookupInfo<MemberMethodDecl>, binds: Map<string, ResolvedType>, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>};
                if(mmd.decl.decl.attributes.includes("virtual") || mmd.decl.decl.attributes.includes("abstract")) {
                    tchecker.processMemberMethodVirtual(mmd.fkey, mmd.decl, mmd.binds, mmd.pcodes, virtualmemberdecls);
                }
                else if(mmd.decl.decl.attributes.includes("override")) {
                    tchecker.processMemberMethodOverride(mmd.fkey, mmd.decl, mmd.declaredecl, mmd.binds, mmd.pcodes);
                }
                else if(mmd.decl.decl.attributes.includes("task_action")) {
                    tchecker.processMemberTaskAction(mmd.fkey, mmd.decl, mmd.binds, mmd.pcodes);
                }
                else {
                    tchecker.processMemberMethodDirect(mmd.fkey, mmd.decl, mmd.binds, mmd.pcodes);
                }
            }
            else if (tchecker.m_pendingCodeDecls.length !== 0) {
                const lmd = tchecker.m_pendingCodeDecls.shift() as {cpdata: TIRCodePack, cpdecl: InvokeDecl, desiredfunc: ResolvedFunctionType, declbinds: TemplateBindScope, bodybinds: Map<string, ResolvedType>, capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, capturedvars: Map<string, {vname: string, vtype: ResolvedType}>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>};
                tchecker.processLambdaFunction(lmd.cpdata, lmd.cpdecl, lmd.desiredfunc, lmd.declbinds, lmd.bodybinds, lmd.capturedpcodes, lmd.capturedvars, lmd.argpcodes);
            }
            else {
                ;
            }

            if(!tchecker.anyPending()) {
                tchecker.updateVirtualPending(virtualmemberdecls);
            }
        }

        //process regex literals + validators decls (regex and path)
        const lvinfo = tchecker.processRegexAndValidatorInfo();

        if(tchecker.m_errors.length !== 0) {
            return { tasm: undefined, errors: tchecker.m_errors.map((ee) => `${ee[2]} -- ${ee[1]} @ ${ee[0]}`) };
        }
        else {
            return { tasm: new TIRAssembly(tchecker.m_tirNamespaceMap, tchecker.m_tirTypeMap, tchecker.m_tirFieldMap, tchecker.m_tirInvokeMap, tchecker.m_tirCodePackMap, lvinfo.literalre, lvinfo.validatorsre, lvinfo.pathvalidators), errors: [] };
        }
    }

    static generateTASM(pckge: PackageConfig[], buildLevel: BuildLevel, istestbuild: boolean, isoverflowfailure: boolean, issmtbuild: boolean, entrypoints: {ns: string, fname: string}[], depsmap: Map<string, string[]>): { tasm: TIRAssembly | undefined, errors: string[] } {
        ////////////////
        //Parse the contents and generate the assembly
        const assembly = new Assembly();
        const allfiles = ([] as [PackageConfig, string, string, string][]).concat(...pckge.map((pk) => pk.src.map((srci) => [pk, srci.srcpath, srci.filename, srci.contents] as [PackageConfig, string, string, string])));

        const p = new Parser(assembly);
        let filetonsnamemap = new Map<string, Set<string>>();
        let nsfilemap = new Map<string, [PackageConfig, string, string, string][]>();
        let allfe: [PackageConfig, string, string, string][] = [];
        try {
            for(let i = 0; i < allfiles.length; ++i) {
                const fe = allfiles[i];
                const deps = p.parseCompilationUnitGetNamespaceDeps(fe[1], fe[3], fe[0].macrodefs);
            
                if(deps === undefined) {
                    return { tasm: undefined, errors: ["Hard failure in parse of namespace deps"] };
                }

                if(deps.ns !== "Core") {
                    deps.deps.push("Core");
                }

                const nsnamemap = ["Core", deps.ns, ...[...deps.remap].map((rrp) => rrp[0])];
                filetonsnamemap.set(fe[1], new Set<string>(nsnamemap));

                if(!depsmap.has(deps.ns)) {
                    depsmap.set(deps.ns, []);
                }
                depsmap.set(deps.ns, [...(depsmap.get(deps.ns) as string[]), ...deps.deps].sort());

                if(!nsfilemap.has(deps.ns)) {
                    nsfilemap.set(deps.ns, []);
                }
                (nsfilemap.get(deps.ns) as [PackageConfig, string, string, string][]).push(fe);
            }

            const allns = [...depsmap].map((dm) => dm[0]).sort();
            let nsdone = new Set<string>();
            while(nsdone.size < allns.length) {
                const nsopts = allns.filter((ns) => {
                    const ndeps = depsmap.get(ns) as string[];
                    return !nsdone.has(ns) && ndeps.every((dep) => nsdone.has(dep));
                });

                if(nsopts.length === 0) {
                    //TODO: should hunt down the cycle -- or misspelled module name
                    return { tasm: undefined, errors: ["Cyclic dependency in namespaces or misspelled import namespace"] };
                }

                const nns = nsopts[0];
                const nsfiles = nsfilemap.get(nns) as [PackageConfig, string, string, string][];

                for (let i = 0; i < nsfiles.length; ++i) {
                    const parseok = p.parseCompilationUnitPass1(nsfiles[i][1], nsfiles[i][3], nsfiles[i][0].macrodefs);
                    if (!parseok || p.getParseErrors() !== undefined) {
                        const parseErrors = p.getParseErrors();
                        if (parseErrors !== undefined) {
                            return { tasm: undefined, errors: parseErrors.map((err: [string, number, string]) => JSON.stringify(err)) };
                        }
                    }
                }
    
                for (let i = 0; i < nsfiles.length; ++i) {
                    const parseok = p.parseCompilationUnitPass2(nsfiles[i][1], nsfiles[i][3], nsfiles[i][0].macrodefs, filetonsnamemap.get(nsfiles[i][1]) as Set<string>);
                    if (!parseok || p.getParseErrors() !== undefined) {
                        const parseErrors = p.getParseErrors();
                        if (parseErrors !== undefined) {
                            return { tasm: undefined, errors: parseErrors.map((err: [string, number, string]) => JSON.stringify(err)) };
                        }
                    }
                }

                allfe = [...allfe, ...nsfiles].sort((a, b) => a[1].localeCompare(b[1]));
                nsdone.add(nns);
            }
        }
        catch (ex) {
            return { tasm: undefined, errors: [`Hard failure in parse with exception -- ${ex}`] };
        }

        //
        //TODO: compute hash of sources here -- maybe bundle for debugging or something too?
        //

        return TypeChecker.processAssembly(assembly, buildLevel, istestbuild, isoverflowfailure, issmtbuild, entrypoints);
    }
}

export { TypeError, TypeChecker };
