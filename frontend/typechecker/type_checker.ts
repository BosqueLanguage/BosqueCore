//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { Assembly, BuildLevel, ConceptTypeDecl, EntityTypeDecl, InfoTemplate, InfoTemplateConst, InfoTemplateMacro, InfoTemplateRecord, InfoTemplateTuple, InfoTemplateValue, InvokeDecl, isBuildLevelEnabled, MemberFieldDecl, MemberMethodDecl, NamespaceConstDecl, NamespaceFunctionDecl, NamespaceOperatorDecl, NamespaceTypedef, OOMemberDecl, OOPTypeDecl, PathValidator, PostConditionDecl, PreConditionDecl, StaticFunctionDecl, StaticMemberDecl, TaskTypeDecl, TemplateTermDecl, TypeConditionRestriction } from "../ast/assembly";
import { ResolvedASCIIStringOfEntityAtomType, ResolvedAtomType, ResolvedConceptAtomType, ResolvedConceptAtomTypeEntry, ResolvedOkEntityAtomType, ResolvedErrEntityAtomType, ResolvedSomethingEntityAtomType, ResolvedMapEntryEntityAtomType, ResolvedEntityAtomType, ResolvedEnumEntityAtomType, ResolvedFunctionType, ResolvedHavocEntityAtomType, ResolvedListEntityAtomType, ResolvedMapEntityAtomType, ResolvedObjectEntityAtomType, ResolvedPathEntityAtomType, ResolvedPathFragmentEntityAtomType, ResolvedPathGlobEntityAtomType, ResolvedPathValidatorEntityAtomType, ResolvedPrimitiveInternalEntityAtomType, ResolvedQueueEntityAtomType, ResolvedRecordAtomType, ResolvedSetEntityAtomType, ResolvedStackEntityAtomType, ResolvedStringOfEntityAtomType, ResolvedTaskAtomType, ResolvedTupleAtomType, ResolvedType, ResolvedTypedeclEntityAtomType, ResolvedValidatorEntityAtomType, TemplateBindScope, ResolvedFunctionTypeParam, ResolvedConstructableEntityAtomType, ResolvedPrimitiveCollectionEntityAtomType } from "./resolved_type";
import { AccessEnvValueExpression, AccessFormatInfoExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndxpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionExpression, ConstantExpressionValue, ConstructorPCodeExpression, ConstructorPrimaryExpression, ConstructorRecordExpression, ConstructorTupleExpression, Expression, ExpressionTag, IfExpression, LiteralASCIIStringExpression, LiteralASCIITemplateStringExpression, LiteralASCIITypedStringExpression, LiteralBoolExpression, LiteralExpressionValue, LiteralFloatPointExpression, LiteralIntegralExpression, LiteralNoneExpression, LiteralNothingExpression, LiteralRationalExpression, LiteralRegexExpression, LiteralStringExpression, LiteralTemplateStringExpression, LiteralTypedPrimitiveConstructorExpression, LiteralTypedStringExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchExpression, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, PCodeInvokeExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAs, PostfixInvoke, PostfixIs, PostfixOp, PostfixOpTag, PrefixNegateOp, PrefixNotOp, SpecialConstructorExpression, SwitchExpression, TaskSelfFieldExpression, TaskSelfActionExpression, TaskGetIDExpression, Statement, EmptyStatement, VariableDeclarationStatement, VariableAssignmentStatement, ReturnStatement, AbortStatement, AssertStatement, DebugStatement, IfStatement, UnscopedBlockStatement, SwitchStatement, MatchStatement, RefCallStatement, EnvironmentFreshStatement, EnvironmentSetStatement, EnvironmentSetStatementBracket, TaskRunStatement, TaskMultiStatement, TaskDashStatement, TaskAllStatement, TaskRaceStatement, TaskSelfControlExpression, TaskCallWithStatement, TaskResultWithStatement, TaskSetStatusStatement, TaskSetSelfFieldStatement, TaskEventEmitStatement, LoggerEmitStatement, LoggerEmitConditionalStatement, LoggerLevelStatement, LoggerCategoryStatement, LoggerPrefixStatement, StatementTag, ScopedBlockStatement, BodyImplementation } from "../ast/body";
import { AndTypeSignature, AutoTypeSignature, FunctionTypeSignature, NominalTypeSignature, ParseErrorTypeSignature, ProjectTypeSignature, RecordTypeSignature, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature } from "../ast/type";
import { FlowTypeTruthOps, ExpressionTypeEnvironment, VarInfo, FlowTypeTruthValue, FlowTypeInfoOption, StatementTypeEnvironment } from "./type_environment";

import { TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessConstMemberFieldExpression, TIRAccessVariableExpression, TIRExpression, TIRInvalidExpression, TIRLiteralASCIIStringExpression, TIRLiteralASCIITemplateStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression, TIRLiteralStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralTypedPrimitiveConstructorExpression, TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedStringExpression, TIRLiteralValue, TIRCoerceSafeExpression, TIRCoerceSafeRefCallResultExpression, TIRCoerceSafeTaskRefCallResultExpression, TIRCoerceSafeActionCallResultExpression, TIRConstructorPrimaryDirectExpression, TIRResultOkConstructorExpression, TIRResultErrConstructorExpression, TIRSomethingConstructorExpression, TIRMapEntryConstructorExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorListExpression, TIRConstructorMapExpression, TIRConstructorTupleExpression, TIRConstructorRecordExpression, TIRCodePack, TIRTypedeclDirectExpression, TIRTypedeclConstructorExpression, TIRCallNamespaceFunctionExpression, TIRCallNamespaceOperatorExpression, TIRBinKeyEqBothUniqueExpression, TIRBinKeyEqOneUniqueExpression, TIRBinKeyEqGeneralExpression, TIRBinKeyUniqueLessExpression, TIRBinKeyGeneralLessExpression, TIRInjectExpression, TIRCallStaticFunctionExpression, TIRLogicActionAndExpression, TIRIsTypeExpression, TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression, TIRIsNoneExpression, TIRIsNotNoneExpression, TIRIsNothingExpression, TIRIsSubTypeExpression, TIRAsNoneExpression, TIRAsNotNoneExpression, TIRAsNothingExpression, TIRAsTypeExpression, TIRAsSubTypeExpression, TIRExtractExpression, TIRCallMemberFunctionSelfRefExpression, TIRCallMemberFunctionExpression, TIRCallMemberFunctionDynamicExpression, TIRPrefixNotExpression, TIRStatement, TIRPrefixNegateExpression, TIRIsNotNothingExpression, TIRIsNotTypeExpression, TIRIsNotSubTypeExpression, TIRBinKeyNeqBothUniqueExpression, TIRBinKeyNeqOneUniqueExpression, TIRBinKeyNeqGeneralExpression, TIRLogicActionOrExpression, TIRBinLogicOrExpression, TIRBinAddExpression, TIRBinSubExpression, TIRBinMultExpression, TIRBinDivExpression, TIRNumericEqExpression, TIRNumericNeqExpression, TIRNumericLessExpression, TIRNumericLessEqExpression, TIRNumericGreaterExpression, TIRNumericGreaterEqExpression, TIRIfExpression, TIRSwitchExpression, TIRMatchExpression, TIRTaskSelfFieldExpression, TIRTaskGetIDExpression, TIRCallMemberActionExpression, TIRVarDeclareStatement, TIRCallMemberFunctionTaskSelfRefExpression, TIRCallMemberFunctionTaskExpression, TIRVarDeclareAndAssignStatementWRef, TIRVarDeclareAndAssignStatementWTaskRef, TIRVarDeclareAndAssignStatementWAction, TIRVarDeclareAndAssignStatement, TIRVarAssignStatementWRef, TIRVarAssignStatementWTaskRef, TIRVarAssignStatementWAction, TIRVarAssignStatement, TIRReturnStatement, TIRReturnStatementWRef, TIRReturnStatementWTaskRef, TIRReturnStatementWAction, TIRAbortStatement, TIRAssertCheckStatement, TIRDebugStatement, TIRBinLogicAndExpression, TIRScopedBlockStatement, TIRUnscopedBlockStatement, TIRIfStatement, TIRNopStatement, TIRSwitchStatement, TIRMatchStatement, TIRCallStatementWRef, TIRCallStatementWTaskRef, TIRCallStatementWAction, TIREnvironmentFreshStatement, TIREnvironmentSetStatement, TIREnvironmentSetStatementBracket, TIRTaskSelfControlExpression, TIRTaskRunStatement, TIRTaskMultiStatement, TIRTaskDashStatement, TIRTaskAllStatement, TIRTaskRaceStatement, TIRTaskSetSelfFieldStatement, TIRLoggerEmitStatement, TIRLoggerEmitConditionalStatement } from "../tree_ir/tir_body";
import { TIRASCIIStringOfEntityType, TIRConceptSetType, TIRConceptType, TIRConstMemberDecl, TIREnumEntityType, TIRErrEntityType, TIRFieldKey, TIRFunctionParameter, TIRHavocEntityType, TIRInvoke, TIRInvokeAbstractDeclaration, TIRInvokeImplementation, TIRInvokeKey, TIRInvokePrimitive, TIRListEntityType, TIRMapEntityType, TIRMapEntryEntityType, TIRMemberFieldDecl, TIRNamespaceConstDecl, TIRNamespaceDeclaration, TIRNamespaceFunctionDecl, TIRNamespaceOperatorDecl, TIRObjectEntityType, TIRObjectInvariantDecl, TIRObjectValidateDecl, TIROkEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPostConditionDecl, TIRPreConditionDecl, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRSomethingEntityType, TIRStackEntityType, TIRStringOfEntityType, TIRTaskType, TIRTupleType, TIRType, TIRTypedeclEntityType, TIRTypedeclInvariantDecl, TIRTypedeclValidateDecl, TIRTypeKey, TIRTypeName, TIRUnionType, TIRValidatorEntityType } from "../tree_ir/tir_assembly";

import { BSQRegex, RegexAlternation, RegexCharRange, RegexComponent, RegexConstClass, RegexDotCharClass, RegexLiteral, RegexOptional, RegexPlusRepeat, RegexRangeRepeat, RegexSequence, RegexStarRepeat } from "../bsqregex";
import { extractLiteralStringValue, extractLiteralASCIIStringValue, SourceInfo } from "../build_decls";

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

        return `<${terms.join(",")}>`;
    }

    static generateInvokeIDForNamespaceFunction(ns: string, name: string, terms: TIRTypeKey[]): TIRInvokeKey {
        return `${ns}::${name}${TIRIDGenerator.generateTermsBinds(terms)}`;
    }

    static generateInvokeIDForNamespaceOperatorBase(ns: string, name: string): TIRInvokeKey {
        return `operator_base_${ns}::${name}`;
    }

    static generateInvokeIDForNamespaceOperatorImpl(ns: string, name: string, idx: number): TIRInvokeKey {
        return `operator_impl_${idx}_${ns}::${name}`;
    }

    static generateInvokeForMemberFunction(ttype: TIRTypeKey, name: string, terms: TIRTypeKey[]): TIRInvokeKey {
        return `${ttype}::${name}${TIRIDGenerator.generateTermsBinds(terms)}`;
    }

    static generateInvokeForMemberMethod(ttype: TIRTypeKey, name: string, terms: TIRTypeKey[]): TIRInvokeKey {
        return `${ttype}::${name}${TIRIDGenerator.generateTermsBinds(terms)}`;
    }

    static generateMemberFieldID(typeid: string, fname: string): TIRFieldKey {
        return `${typeid}$${fname}`;
    }
}

class TypeChecker {
    private readonly m_assembly: Assembly;
    private m_buildLevel: BuildLevel;

    private m_file: string;
    private m_rtype: ResolvedType;
    private m_taskOpsOk: boolean;
    private m_taskSelfOk: "no" | "read" | "write";
    private m_taskType: {taskdecl: TaskTypeDecl, taskbinds: Map<string, ResolvedType>} | undefined;
    private m_errors: [string, number, string][];

    private m_specialTypeMap: Map<string, ResolvedType> = new Map<string, ResolvedType>();

    private m_subtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();
    private m_atomSubtypeRelationMemo: Map<string, Map<string, boolean>> = new Map<string, Map<string, boolean>>();

    private m_typedeclResolutions: Map<string, ResolvedType> = new Map<string, ResolvedType>();

    private m_tirTypeMap: Map<string, TIRType> = new Map<string, TIRType>();
    private m_tirNamespaceMap: Map<string, TIRNamespaceDeclaration> = new Map<string, TIRNamespaceDeclaration>();
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

    constructor(assembly: Assembly, buildlevel: BuildLevel, overflowisfailure: boolean) {
        this.m_assembly = assembly;

        this.m_buildLevel = buildlevel;

        this.m_file = "[No File]";
        this.m_rtype = this.getSpecialNoneType();
        this.m_taskOpsOk = false;
        this.m_taskSelfOk = "no";
        this.m_errors = [];
        
        TIRExpression.OverflowIsFailure = overflowisfailure;
    }

    initializeForBody(file: string, rtype: ResolvedType, taskok: boolean, selfok: "no" | "read" | "write") {
        this.m_file = file;
        this.m_rtype = rtype;
        this.m_taskOpsOk = taskok;
        this.m_taskSelfOk = selfok;
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

    private envExpressionCollapseFlowInfos(infos: FlowTypeInfoOption[]): FlowTypeInfoOption {
        const itype = this.normalizeUnionList(infos.map((ii) => ii.tinfer));

        const allexps = ([] as string[]).concat(...infos.map((ii) => [...ii.expInferInfo].map((vv) => vv[0])));
        const iexps = allexps.filter((ename) => infos.every((ii) => ii.expInferInfo.has(ename)));

        const expinfo = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>();
        iexps.forEach((ename) => {
            const deps = (infos[0].expInferInfo.get(ename) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}).depvars;
            const iopts = this.normalizeUnionList(infos.map((ii) => (ii.expInferInfo.get(ename) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}).infertype));

            expinfo.set(ename, {depvars: deps, infertype: iopts, infertruth: FlowTypeTruthValue.Unknown});
        });

        return new FlowTypeInfoOption(itype, FlowTypeTruthValue.Unknown, expinfo);
    }

    private envExpressionCollapseStatmentFlows(infos: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>[]): Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}> {
        const allexps = ([] as string[]).concat(...infos.map((ii) => [...ii].map((vv) => vv[0])));
        const iexps = allexps.filter((ename) => infos.every((ii) => ii.has(ename)));

        const expinfo = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>();
        iexps.forEach((ename) => {
            const deps = (infos[0].get(ename) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}).depvars;
            const iopts = this.normalizeUnionList(infos.map((ii) => (ii.get(ename) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}).infertype));

            expinfo.set(ename, {depvars: deps, infertype: iopts, infertruth: FlowTypeTruthValue.Unknown});
        });

        return expinfo;
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
            if(ofc.conceptTypes.length === 1 && ofc.conceptTypes[0].concept.attributes.includes("__adt_concept_type")) {
                const splits = [...this.m_assembly.getAllEntities()]
                    .filter((tt) => tt.terms.length === 0)
                    .map((tt) => ResolvedObjectEntityAtomType.create(tt, new Map<string, ResolvedType>()))
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

        if (!(ttype.tryGetUniqueEntityTypeInfo() instanceof ResolvedTypedeclEntityAtomType)) {
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

            const strof = validators.strof !== undefined ? ({vtype: validators.strof.typeID, vre: this.processValidatorRegex(rtype.object.sourceLocation, validators.strof.typeID)}) : undefined;
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

            tirtype = new TIRValidatorEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, this.processValidatorRegex(rtype.object.sourceLocation, rtype.typeID));
        }
        else if(rtype instanceof ResolvedStringOfEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));            
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));

            const revalidator = this.processValidatorRegex(rtype.object.sourceLocation, rtype.typeID);
            
            tirtype = new TIRStringOfEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, validator, revalidator);
        }
        else if(rtype instanceof ResolvedASCIIStringOfEntityAtomType) {
            const validator = this.toTIRTypeKey(ResolvedType.createSingle(rtype.validatortype));
            const tname = new TIRTypeName(rtype.object.ns, rtype.object.name, [validator]);
            const supertypes = this.resolveProvides(rtype.object, TemplateBindScope.createSingleBindScope("T", ResolvedType.createSingle(rtype.validatortype))).map((rr) => this.toTIRTypeKey(rr));

            const revalidator = this.processValidatorRegex(rtype.object.sourceLocation, rtype.typeID);
            
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
            
            tirtype = new TIRMapEntityType(rtype.typeID, tname, rtype.object.sourceLocation, rtype.object.srcFile, rtype.object.attributes, supertypes, typek, typev);
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

            const mainfunc = {mkey: TIRIDGenerator.generateInvokeForMemberFunction(rtype.typeID, rtype.task.mainfunc.name, []), mname: rtype.task.mainfunc.name};
            const onfuncs = {
                onCanel: rtype.task.onfuncs.onCanel !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.onfuncs.onCanel.name, [])) : undefined, 
                onFailure: rtype.task.onfuncs.onFailure !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.onfuncs.onFailure.name, [])) : undefined, 
                onTimeout: rtype.task.onfuncs.onTimeout !== undefined ? (TIRIDGenerator.generateInvokeForMemberMethod(rtype.typeID, rtype.task.onfuncs.onTimeout.name, [])) : undefined, 
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
            assert(false, `Unknown type to convert ${rtype.typeID}`);
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

    restrictNone(from: ResolvedType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        return this.splitTypes(from, this.getSpecialNoneType());
    }

    restrictSome(from: ResolvedType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        return this.splitTypes(from, this.getSpecialSomeConceptType());
    }

    restrictNothing(from: ResolvedType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        return this.splitTypes(from, this.getSpecialNothingType());
    }

    restrictSomething(from: ResolvedType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
        return this.splitTypes(from, this.getSpecialISomethingConceptType());
    }

    restrictT(from: ResolvedType, t: ResolvedType): { tp: ResolvedType | undefined, fp: ResolvedType | undefined } {
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
        return this.setResultExpressionBoolPassThrough(env, new TIRCoerceSafeExpression(sinfo, env.expressionResult, this.toTIRTypeKey(this.envExpressionGetInferType(env)), this.toTIRTypeKey(trgttype)), trgttype);
    }

    private emitSafeCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        return this.setResultExpressionBoolPassThrough(env, new TIRCoerceSafeExpression(sinfo, env.expressionResult, this.toTIRTypeKey(this.envExpressionGetInferType(env)), this.toTIRTypeKey(trgttype)), trgttype);
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
        return this.setResultExpression(env, new TIRCoerceSafeRefCallResultExpression(sinfo, env.expressionResult, this.toTIRTypeKey(this.envExpressionGetInferType(env)), this.toTIRTypeKey(trgttype)), trgttype);
    }

    private emitTaskRefCallCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        this.raiseErrorIf(sinfo, !this.subtypeOf(this.envExpressionGetInferType(env), trgttype), `Cannot convert type ${this.envExpressionGetInferType(env)} into ${trgttype.typeID}`);
        return this.setResultExpression(env, new TIRCoerceSafeTaskRefCallResultExpression(sinfo, env.expressionResult, this.toTIRTypeKey(this.envExpressionGetInferType(env)), this.toTIRTypeKey(trgttype)), trgttype);
    }

    private emitActionCallCoerceIfNeeded(env: ExpressionTypeEnvironment, sinfo: SourceInfo, trgttype: ResolvedType): ExpressionTypeEnvironment {
        if(env.trepr.isSameType(trgttype)) {
            return env;
        }

        this.raiseErrorIf(sinfo, !this.subtypeOf(this.envExpressionGetInferType(env), trgttype), `Cannot convert type ${this.envExpressionGetInferType(env)} into ${trgttype.typeID}`);
        return this.setResultExpression(env, new TIRCoerceSafeActionCallResultExpression(sinfo, env.expressionResult, this.toTIRTypeKey(this.envExpressionGetInferType(env)), this.toTIRTypeKey(trgttype)), trgttype);
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
        const eenvs = args.map((arg, ii) => {
            if (/*arg is codepack*/) {
                return xxxx;
            }
            else {
                return this.checkExpression(env, arg, this.normalizeTypeOnly(expectedtypes[ii], fbinds));
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

        const vv = this.processValidatorRegex(exp.sinfo, toftype.typeID);
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

        const vv = this.processValidatorRegex(exp.sinfo, toftype.typeID);
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
        const lexp = this.reduceLiteralValueToCanonicalForm(exp.value, env.binds);
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
            return this.emitCoerceIfNeeded(this.checkExpression(env, cexp, rtype), exp.sinfo, rtype);
        }
        else {
            const tirrtype = this.toTIRTypeKey(rtype);

            this.m_pendingNamespaceConsts.push(cdecl);
            return this.setResultExpression(env, new TIRAccessNamespaceConstantExpression(exp.sinfo, exp.ns, exp.name, tirrtype), rtype);
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
            return this.setResultExpression(env, new TIRAccessConstMemberFieldExpression(exp.sinfo, tirdecltype, exp.name, tirrtype), rtype);
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

                //No terms to be bound on operator call

                this.m_pendingNamespaceOperators.push({decl: opsintro as NamespaceOperatorDecl, impls: opdecls})

                const fkey = TIRIDGenerator.generateInvokeIDForNamespaceOperatorBase(nsdecl.ns, exp.name);
                const rtype = this.normalizeTypeOnly((opsintro as NamespaceOperatorDecl).invoke.resultType, TemplateBindScope.createEmptyBindScope());
                const tirrtype = this.toTIRTypeKey(rtype);

                const argexps = this.checkArgumentList(exp.sinfo, env, exp.args, (opsintro as NamespaceOperatorDecl).invoke.params.map((pp) => pp.type), TemplateBindScope.createEmptyBindScope());

                const tircall = new TIRCallNamespaceOperatorExpression(exp.sinfo, nsdecl.ns, exp.name, fkey, tirrtype, argexps);
                return this.setResultExpression(env, tircall, rtype);
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

                const fkey = TIRIDGenerator.generateInvokeIDForNamespaceFunction(nsdecl.ns, exp.name, fdecl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
                const rtype = this.normalizeTypeOnly(fdecl.invoke.resultType, TemplateBindScope.createBaseBindScope(binds));
                const tirrtype = this.toTIRTypeKey(rtype);

                const argexps = this.checkArgumentList(exp.sinfo, env, exp.args, fdecl.invoke.params.map((pp) => pp.type), TemplateBindScope.createBaseBindScope(binds));

                const tircall = new TIRCallNamespaceFunctionExpression(exp.sinfo, nsdecl.ns, exp.name, fkey, tirrtype, argexps);
                return this.setResultExpression(env, tircall, rtype);
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
                const fkey = TIRIDGenerator.generateInvokeForMemberFunction(this.toTIRTypeKey(fdecl.ttype), exp.name, fdecl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
            
                this.m_pendingFunctionMemberDecls.push({decl: fdecl, binds: binds});

                const tircall = new TIRCallStaticFunctionExpression(exp.sinfo, this.toTIRTypeKey(fdecl.ttype), exp.name, fkey, tirrtype, argexps);
                return this.setResultExpression(env, tircall, rtype);
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
        const tiroftype = this.toTIRTypeKey(this.envExpressionGetInferType(env));

        const idxtype = (this.envExpressionGetInferType(env).options[0] as ResolvedTupleAtomType).types[op.index];
        const tiridxtype = this.toTIRTypeKey(idxtype);

        return this.setResultExpression(env, new TIRLoadIndexExpression(op.sinfo, env.expressionResult, tiroftype, op.index, tiridxtype), idxtype);
    }

    private checkAccessFromName(env: ExpressionTypeEnvironment, op: PostfixAccessFromName): ExpressionTypeEnvironment {
        const isrecord = this.envExpressionGetInferType(env).options.every((atom) => atom instanceof TIRRecordType);
        const isobj = this.envExpressionGetInferType(env).options.every((atom) => atom instanceof ResolvedEntityAtomType);

        this.raiseErrorIf(op.sinfo, !isrecord && !isobj, `Cannot load the named location ${op.name} from type ${this.envExpressionGetInferType(env)}`);
        const tiroftype = this.toTIRTypeKey(this.envExpressionGetInferType(env));

        if (isrecord) {
            this.raiseErrorIf(op.sinfo, this.envExpressionGetInferType(env).options.some((atom) => (atom as ResolvedRecordAtomType).entries.find((entry) => entry.pname === op.name) === undefined), `Property "${op.name}" not be defined for record`);

            const rtype = ((this.envExpressionGetInferType(env).options[0] as ResolvedRecordAtomType).entries.find((entry) => entry.pname === op.name) as {pname: string, ptype: ResolvedType}).ptype;
            const tirrtype = this.toTIRTypeKey(rtype);

            this.raiseErrorIf(op.sinfo, this.envExpressionGetInferType(env).options.length === 0, "only non-virtual property loads are supported for now");
            return this.setResultExpression(env, new TIRLoadPropertyExpression(op.sinfo, env.expressionResult, tiroftype, op.name, tirrtype), rtype);
        }
        else {
            const fftry = this.resolveMemberField(op.sinfo, this.envExpressionGetInferType(env), op.name);
            this.raiseErrorIf(op.sinfo, fftry === undefined, `Could not resolve field "${op.name}" on type ${this.envExpressionGetInferType(env).typeID}`);
            const ff = fftry as OOMemberLookupInfo<MemberFieldDecl>;

            const fftype = this.normalizeTypeOnly(ff.decl.declaredType, TemplateBindScope.createBaseBindScope(ff.oobinds));
            const tirfftype = this.toTIRTypeKey(fftype);

            const fkey = TIRIDGenerator.generateMemberFieldID(this.toTIRTypeKey(ff.ttype), op.name);

            if(ff.ootype instanceof EntityTypeDecl) {
                return this.setResultExpression(env, new TIRLoadFieldExpression(op.sinfo, tiroftype, env.expressionResult, fkey, tirfftype), fftype);
            }
            else {
                return this.setResultExpression(env, new TIRLoadFieldVirtualExpression(op.sinfo, tirfftype, env.expressionResult, fkey, tirfftype), fftype);
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

            const tkey = this.toTIRTypeKey(mresolve.impl[0].ttype);
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
                const fkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
                this.m_pendingMethodMemberDecls.push({decl: knownimpl, binds: binds}, {decl: mresolve.decl, binds: binds});

                const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.impl[0].ttype);
                this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.isThisRef && !(mresolve.impl[0].ootype instanceof EntityTypeDecl), `self call with ref can only be done on non-virtual methods defined on entities but got ${mresolve.impl[0].ttype.typeID}`);

                if (mresolve.decl.decl.invoke.isThisRef) {
                    return this.setResultExpression(env, new TIRCallMemberFunctionSelfRefExpression(op.sinfo, tkey, op.name, fkey, tirrtype, refvar as string, rcvrexp.expressionResult, argexps), rtype);
                }
                else {
                    return this.setResultExpression(env, new TIRCallMemberFunctionExpression(op.sinfo, tkey, op.name, fkey, tirrtype, rcvrexp.expressionResult, argexps), rtype);
                }
            }
        }
        else {
            this.raiseErrorIf(op.sinfo, mresolve.decl.decl.invoke.isThisRef, "cannot use ref on virtual method call -- variance on updated this ref type");
            const tkey = this.toTIRTypeKey(mresolve.decl.ttype);
            const declkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
            this.m_pendingMethodMemberDecls.push({decl: mresolve.decl, binds: binds});

            const inferthistype = this.toTIRTypeKey(this.envExpressionGetInferType(env));
            let inferfkey: TIRInvokeKey | undefined = undefined;
            if(mresolve.impl.length === 1) {
                const tirimpltype = this.toTIRTypeKey(mresolve.impl[0].ttype);
                inferfkey = TIRIDGenerator.generateInvokeForMemberMethod(tirimpltype, op.name, mresolve.decl.decl.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
                this.m_pendingMethodMemberDecls.push({decl: mresolve.impl[0], binds: binds});
            }

            const rcvrexp = this.emitCoerceIfNeeded(env, op.sinfo, mresolve.decl.ttype);
            return this.setResultExpression(env, new TIRCallMemberFunctionDynamicExpression(op.sinfo, tkey, op.name, declkey, inferthistype, inferfkey, tirrtype, rcvrexp.expressionResult, argexps), rtype);
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
        return this.setResultExpressionBoolNegate(benv, new TIRPrefixNotExpression(exp.sinfo, benv.expressionResult), this.getSpecialBoolType());
    }

    private checkPrefixNegateOpExpression(env: ExpressionTypeEnvironment, exp: PrefixNegateOp): ExpressionTypeEnvironment {
        const nenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env, exp.exp, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(nenv.trepr.options), `expected a numeric type but got ${nenv.trepr.typeID}`);

        const ntype = ResolvedType.getNumericBaseRepresentation(nenv.trepr.options);
        this.raiseErrorIf(exp.sinfo, ntype.typeID === "Nat" || ntype.typeID === "BigNat", `cannot negage unsigned type ${nenv.trepr.typeID}`);
        
        return this.setResultExpression(nenv, new TIRPrefixNegateExpression(exp.sinfo, nenv.expressionResult, this.toTIRTypeKey(nenv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(ntype))), nenv.trepr)
    }

    private checkBinAddExpression(env: ExpressionTypeEnvironment, exp: BinAddExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `addition is defined on numeric values of same type but got -- ${lenv.trepr.typeID} + ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRBinAddExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(renv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(nntype))), renv.trepr);
    }

    private checkBinSubExpression(env: ExpressionTypeEnvironment, exp: BinSubExpression): ExpressionTypeEnvironment {
        const lenv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.lhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(lenv.trepr.options), `expected a numeric type but got ${lenv.trepr.typeID}`);

        const renv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), exp.rhs, undefined), exp.sinfo);
        this.raiseErrorIf(exp.sinfo, !ResolvedType.isNumericType(renv.trepr.options), `expected a numeric type but got ${renv.trepr.typeID}`);

        this.raiseErrorIf(exp.sinfo, lenv.trepr.isSameType(renv.trepr), `subtraction is defined on numeric values of same type but got -- ${lenv.trepr.typeID} - ${renv.trepr.typeID}`);
        const nntype = ResolvedType.getNumericBaseRepresentation(renv.trepr.options);

        return this.setResultExpression(env, new TIRBinSubExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(renv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(nntype))), renv.trepr);
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
            return this.setResultExpression(env, new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(lenv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
        }
        else if((lnt instanceof ResolvedTypedeclEntityAtomType) && (rnt instanceof ResolvedTypedeclEntityAtomType)) {
            return this.setResultExpression(env, new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb)), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnb));
        }
        else {
            this.raiseErrorIf(exp.sinfo, (lnt instanceof ResolvedTypedeclEntityAtomType) || (rnt instanceof ResolvedTypedeclEntityAtomType), `multiplication requires at least on unit typed value but got ${lnt.typeID} * ${rnt.typeID}`);

            if(lnt instanceof ResolvedTypedeclEntityAtomType) {
                return this.setResultExpression(env, new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(lenv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
            }
            else {
                return this.setResultExpression(env, new TIRBinMultExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(renv.trepr), this.toTIRTypeKey(ResolvedType.createSingle(rnb))), ResolvedType.createSingle(rnt));
            }
        }
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
            return this.setResultExpression(env, new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnt)), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
        }
        else if((lnt instanceof ResolvedTypedeclEntityAtomType) && (rnt instanceof ResolvedTypedeclEntityAtomType)) {
            return this.setResultExpression(env, new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnb)), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnb));
        }
        else {
            this.raiseErrorIf(exp.sinfo, !(rnt instanceof ResolvedPrimitiveInternalEntityAtomType), `division requires a typed number as numerator and a typed number or a unit type as divisor but got ${lnt.typeID} / ${rnt.typeID}`);

            return this.setResultExpression(env, new TIRBinDivExpression(exp.sinfo, lenv.expressionResult, renv.expressionResult, this.toTIRTypeKey(ResolvedType.createSingle(lnt)), this.toTIRTypeKey(ResolvedType.createSingle(lnb))), ResolvedType.createSingle(lnt));
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

        const andexp = new TIRBinLogicAndExpression(exp.sinfo, lhs.expressionResult, rhs.expressionResult);
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
                const tvaltry = this.reduceLiteralValueToCanonicalForm((exp.switchflow[i].condlit as LiteralExpressionValue).exp, env.binds);
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
                
                cenv = fexp.setResultExpressionInfo(venv.expressionResult, venv.trepr, cflow.fenvs);
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
                    this.raiseErrorIf(exp.sinfo, i == exp.matchflow.length - 1, `exhaustive none check should be last option in match expression but there were ${exp.matchflow.length - (i + 1)} more that are unreachable`);

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
                
                    cenv = fexp.setResultExpressionInfo(venv.expressionResult, venv.trepr, cflow.fenvs);
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

        const fkey = TIRIDGenerator.generateMemberFieldID(this.toTIRTypeKey(tasktype), exp.sfield);
        return this.setResultExpression(env, new TIRTaskSelfFieldExpression(exp.sinfo, this.toTIRTypeKey(tasktype), fkey, exp.sfield, tirfftype), fftype);
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

        return this.setResultExpression(env, new TIRTaskSelfControlExpression(exp.sinfo, tirtask, tirffctl), ffctl);
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

        const fkey = TIRIDGenerator.generateInvokeForMemberMethod(tirdecltype, exp.name, mresolve.invoke.terms.map((tt) => this.toTIRTypeKey(binds.get(tt.name) as ResolvedType)));
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
        this.raiseErrorIf(sinfo, env.isVarNameDefined(vname), `${vname} cannot shadow previous definition`);

        const infertype = rhs !== undefined ? this.envExpressionGetInferType(rhs) : undefined;
        this.raiseErrorIf(sinfo, infertype === undefined && isConst, "must define const var at declaration site");
        this.raiseErrorIf(sinfo, infertype === undefined && decltype instanceof AutoTypeSignature, "must define auto typed var at declaration site");

        const vtype = (decltype instanceof AutoTypeSignature) ? infertype as ResolvedType : this.normalizeTypeOnly(decltype, env.binds);
        this.raiseErrorIf(sinfo, infertype !== undefined && !this.subtypeOf(infertype, vtype), `expression is not of declared type ${vtype.typeID}`);

        return env.addVar(vname, isConst, vtype, infertype !== undefined, rhs !== undefined ? this.envExpressionCollapseFlowInfos(rhs.flowinfo) : undefined);
    }

    private checkAssignSingleVariableExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vname: string, rhs: ExpressionTypeEnvironment): StatementTypeEnvironment {
        const vinfo = env.lookupVar(vname);
        this.raiseErrorIf(sinfo, vinfo === null, `Variable ${vname} was not previously defined`);
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, `Variable ${vname} is defined as const`);

        this.raiseErrorIf(sinfo, !this.subtypeOf(this.envExpressionGetInferType(rhs), (vinfo as VarInfo).declaredType), `Assign value (${this.envExpressionGetInferType(rhs).typeID}) is not subtype of declared variable type ${(vinfo as VarInfo).declaredType}`);

        return env.setVar(vname, this.envExpressionCollapseFlowInfos(rhs.flowinfo));
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

    private checkRefCallStatement(env: StatementTypeEnvironment, stmt: RefCallStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const ee = this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.call, undefined);

        if (ee.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
            const nenv = env.setFlowInfo(this.envExpressionCollapseFlowInfos(this.envClearExps(ee, ee.expressionResult.thisref).flowinfo).expInferInfo);

            return [nenv, [new TIRCallStatementWRef(stmt.sinfo, ee.expressionResult, ee.expressionResult.thisref)]];
        }
        else if (ee.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
            const nenv = env.setFlowInfo(this.envExpressionCollapseFlowInfos(this.envClearExps(ee, "self").flowinfo).expInferInfo);

            return [nenv, [new TIRCallStatementWTaskRef(stmt.sinfo, ee.expressionResult, ee.expressionResult.tsktype)]];
        }
        else if (ee.expressionResult instanceof TIRCallMemberActionExpression) {
            const nenv = env.setFlowInfo(this.envExpressionCollapseFlowInfos(this.envClearExps(ee, "self").flowinfo).expInferInfo);

            return [nenv, [new TIRCallStatementWAction(stmt.sinfo, ee.expressionResult, ee.expressionResult.tsktype)]];
        }
        else {
            this.raiseError(stmt.sinfo, `Unknown op kind ${ee.expressionResult.tag}`);
            return [env, [new TIRNopStatement(stmt.sinfo)]];
        }
    } 

    private checkReturnStatement(env: StatementTypeEnvironment, stmt: ReturnStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const rval = this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.value, this.m_rtype), stmt.value.sinfo, this.m_rtype);

        let rexp: TIRStatement | undefined = undefined;
        if (rval.expressionResult instanceof TIRCallMemberFunctionSelfRefExpression) {
            this.raiseErrorIf(stmt.sinfo, rval.expressionResult.thisref !== "this", "return on ref call not using this as reciever");
            const rhsconv = this.emitRefCallCoerceIfNeeded(rval, stmt.sinfo, this.m_rtype);

            rexp = new TIRReturnStatementWRef(stmt.sinfo, rhsconv.expressionResult);
        }
        else if (rval.expressionResult instanceof TIRCallMemberFunctionTaskSelfRefExpression) {
            const rhsconv = this.emitTaskRefCallCoerceIfNeeded(rval, stmt.sinfo, this.m_rtype);
            rexp = new TIRReturnStatementWTaskRef(stmt.sinfo, rhsconv.expressionResult);
        }
        else if (rval.expressionResult instanceof TIRCallMemberActionExpression) {
            const rhsconv = this.emitActionCallCoerceIfNeeded(rval, stmt.sinfo, this.m_rtype);
            rexp = new TIRReturnStatementWAction(stmt.sinfo, rhsconv.expressionResult);
        }
        else {
            const rhsconv = this.emitCoerceIfNeeded(rval, stmt.sinfo, this.m_rtype);
            rexp = new TIRReturnStatement(stmt.sinfo, rhsconv.expressionResult);
        }

        return [env.endOfExecution(), [rexp as TIRStatement]];
    }

    private checkAbortStatement(env: StatementTypeEnvironment, stmt: AbortStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return [env.endOfExecution(), [new TIRAbortStatement(stmt.sinfo, "Abort")]];
    }

    private checkAssertStatement(env: StatementTypeEnvironment, stmt: AssertStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const test = this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.cond, this.getSpecialBoolType());

        this.raiseErrorIf(stmt.sinfo, !this.subtypeOf(this.envExpressionGetInferType(test), this.getSpecialBoolType()), "Type of logic op must be Bool");

        const tflows = this.convertToBoolFlowsOnResult(test);
        this.raiseErrorIf(stmt.sinfo, tflows.tenvs.length === 0, "assertion will always fail -- use abort instead");
        this.raiseErrorIf(stmt.sinfo, tflows.fenvs.length === 0, "assertion is always true -- remove redundant check?");

        const fenv = stmt.level === "release" ? env.setFlowInfo(this.envExpressionCollapseFlowInfos(tflows.tenvs).expInferInfo) : env;

        if (!isBuildLevelEnabled(stmt.level, this.m_buildLevel)) {
            return [fenv, []];
        }
        else {
            const astmt = new TIRAssertCheckStatement(stmt.sinfo, test.expressionResult, `Assertion failed -- ${this.m_file} : ${stmt.sinfo}`);
            return [fenv, [astmt]];
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

    private checkIfStatement(env: StatementTypeEnvironment, stmt: IfStatement): [StatementTypeEnvironment, TIRStatement[]] {
        let cenv = env.createInitialEnvForExpressionEval();
        let results: {test: ExpressionTypeEnvironment, value: [StatementTypeEnvironment, TIRScopedBlockStatement]}[] = [];

        for (let i = 0; i < stmt.condflow.length; ++i) {
            const testenv = this.emitCoerceIfNeeded(this.checkExpression(cenv, stmt.condflow[i].cond, undefined), stmt.condflow[i].cond.sinfo, this.getSpecialBoolType());
            this.raiseErrorIf(stmt.sinfo, this.envExpressionGetInferTruth(testenv) !== FlowTypeTruthValue.Unknown, "Test is always true/false");

            const cflow = this.convertToBoolFlowsOnResult(testenv);
            
            const trueenv = this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cflow.tenvs).expInferInfo), stmt.condflow[i].value);
            results.push({test: testenv, value: trueenv});
                
            cenv = testenv.createFreshFlowEnvExpressionFrom(cflow.fenvs);
        }
        const aenv = stmt.elseflow !== undefined ? this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cenv.flowinfo).expInferInfo), stmt.elseflow) : ([env.endOfExecution(), new TIRScopedBlockStatement([new TIRNopStatement(stmt.sinfo)], false)] as [StatementTypeEnvironment, TIRScopedBlockStatement]);

        const rexp = new TIRIfStatement(stmt.sinfo, {test: results[0].test.expressionResult, value: results[0].value[1]}, results.slice(1).map((ffp) => {return {test: ffp.test.expressionResult, value: ffp.value[1] };}), aenv[1]);
        const rflows = [...results.map((ff) => ff.value[0]), aenv[0]].filter((es) => !es.isDeadFlow);
        if(rflows.length === 0) {
            return [env.endOfExecution(), [rexp]];
        }
        else {
            return [env.setFlowInfo(this.envExpressionCollapseStatmentFlows(rflows.map((ff) => ff.flowinfo))), [rexp]];
        }
    }

    private checkSwitchStatement(env: StatementTypeEnvironment, stmt: SwitchStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const venv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.sval, undefined), stmt.sval.sinfo);
        
        let cenv: ExpressionTypeEnvironment = venv;
        let exhaustive = false;
        let results: {test: TIRLiteralValue | undefined, value: [StatementTypeEnvironment, TIRScopedBlockStatement]}[] = [];
        for (let i = 0; i < stmt.switchflow.length; ++i) {
            //it is a wildcard match
            if(stmt.switchflow[i].condlit === undefined) {
                this.raiseErrorIf(stmt.sinfo, i == stmt.switchflow.length - 1, `wildcard should be last option in switch statement but there were ${stmt.switchflow.length - (i + 1)} more that are unreachable`);

                const trueenv = this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cenv.flowinfo).expInferInfo), stmt.switchflow[i].value);

                results.push({test: undefined, value: trueenv});
                exhaustive = true;
                break;
            }
            else {
                const tvaltry = this.reduceLiteralValueToCanonicalForm((stmt.switchflow[i].condlit as LiteralExpressionValue).exp, env.binds);
                this.raiseErrorIf((stmt.switchflow[i].condlit as LiteralExpressionValue).exp.sinfo, tvaltry[0] === undefined, `could not resolve literal value`);
                const tval = tvaltry[0] as TIRLiteralValue;

                let fexp: ExpressionTypeEnvironment | undefined = undefined;
                if(tval.exp instanceof TIRLiteralNoneExpression) {
                    this.raiseErrorIf(tval.exp.sinfo, !this.subtypeOf(this.getSpecialNoneType(), this.envExpressionGetInferType(cenv)), `switch argument is never "none" so this case is never possible`);

                    if(this.envExpressionGetInferType(cenv).isNoneType()) {
                        this.raiseErrorIf(stmt.sinfo, i == stmt.switchflow.length - 1, `exhaustive none check should be last option in switch statement but there were ${stmt.switchflow.length - (i + 1)} more that are unreachable`);

                        const trueenv = this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cenv.flowinfo).expInferInfo), stmt.switchflow[i].value);
                        results.push({test: undefined, value: trueenv});
                        exhaustive = true;
                        break;
                    }

                    fexp = this.processTypeIs(tval.exp.sinfo, cenv, this.getSpecialNoneType());
                }
                else if(tval.exp instanceof TIRLiteralNothingExpression) {
                    this.raiseErrorIf(tval.exp.sinfo, !this.subtypeOf(this.getSpecialNothingType(), this.envExpressionGetInferType(cenv)), `switch argument is never "nothing" so this case is never possible`);

                    if(this.envExpressionGetInferType(cenv).isNothingType()) {
                        this.raiseErrorIf(stmt.sinfo, i == stmt.switchflow.length - 1, `exhaustive nothing check should be last option in switch statement but there were ${stmt.switchflow.length - (i + 1)} more that are unreachable`);

                        const trueenv = this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cenv.flowinfo).expInferInfo), stmt.switchflow[i].value);
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

                const trueenv = this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cflow.tenvs).expInferInfo), stmt.switchflow[i].value);
                results.push({test: tval, value: trueenv});
                
                cenv = fexp.setResultExpressionInfo(venv.expressionResult, venv.trepr, cflow.fenvs);
            }
        }

        const clauses = results
            .filter((ffp) => ffp.test !== undefined)
            .map((ffp) => { return { match: ffp.test as TIRLiteralValue, value: ffp.value[1] };});
        const edefault = results.find((ffp) => ffp.test === undefined) ? results[results.length - 1].value[1] : undefined;

        const rexp = new TIRSwitchStatement(stmt.sinfo, venv.expressionResult, clauses, edefault, exhaustive);
        const rflows = [...results.map((ff) => ff.value[0])].filter((es) => !es.isDeadFlow);
        if(rflows.length === 0) {
            return [env.endOfExecution(), [rexp]];
        }
        else {
            return [env.setFlowInfo(this.envExpressionCollapseStatmentFlows(rflows.map((ff) => ff.flowinfo))), [rexp]];
        }
    }

    private checkMatchStatement(env: StatementTypeEnvironment, stmt: MatchStatement): [StatementTypeEnvironment, TIRStatement[]] {
        const venv = this.emitCoerceToInferTypeIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.sval, undefined), stmt.sval.sinfo);
        
        let cenv: ExpressionTypeEnvironment = venv;
        let exhaustive = false;
        let results: {test: TIRExpression | undefined, ttype: TIRTypeKey | undefined, value: [StatementTypeEnvironment, TIRScopedBlockStatement]}[] = [];
        for (let i = 0; i < stmt.matchflow.length; ++i) {
            //it is a wildcard match
            if(stmt.matchflow[i].mtype === undefined) {
                this.raiseErrorIf(stmt.sinfo, i == stmt.matchflow.length - 1, `wildcard should be last option in match statement but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);

                const trueenv = this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cenv.flowinfo).expInferInfo), stmt.matchflow[i].value);

                results.push({test: undefined, ttype: undefined, value: trueenv});
                exhaustive = true;
                break;
            }
            else {
                const testtype = this.normalizeTypeOnly(stmt.matchflow[i].mtype as TypeSignature, env.binds);

                if(this.subtypeOf(this.envExpressionGetInferType(cenv), testtype)) {
                    this.raiseErrorIf(stmt.sinfo, i == stmt.matchflow.length - 1, `exhaustive none check should be last option in match statement but there were ${stmt.matchflow.length - (i + 1)} more that are unreachable`);

                    const trueenv = this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cenv.flowinfo).expInferInfo), stmt.matchflow[i].value);
                    results.push({test: undefined, ttype: undefined, value: trueenv});
                    exhaustive = true;
                    break;
                }
                else {
                    const fexp = this.processTypeIs((stmt.matchflow[i].mtype as TypeSignature).sinfo, cenv, testtype);
                    const cflow = this.convertToBoolFlowsOnResult(fexp);

                    const trueenv = this.checkScopedBlockStatement(env.setFlowInfo(this.envExpressionCollapseFlowInfos(cflow.tenvs).expInferInfo), stmt.matchflow[i].value);
                    results.push({test: fexp.expressionResult, ttype: this.toTIRTypeKey(testtype), value: trueenv});
                
                    cenv = fexp.setResultExpressionInfo(venv.expressionResult, venv.trepr, cflow.fenvs);
                }
            }
        }

        const clauses = results
            .filter((ffp) => ffp.test !== undefined)
            .map((ffp) => { return { match: ffp.test as TIRExpression, mtype: ffp.ttype as TIRTypeKey, value: ffp.value[1] };});
        const edefault = results.find((ffp) => ffp.test === undefined) ? results[results.length - 1].value[1] : undefined;

        const rexp = new TIRMatchStatement(stmt.sinfo, venv.expressionResult, clauses, edefault, exhaustive);
        const rflows = [...results.map((ff) => ff.value[0])].filter((es) => !es.isDeadFlow);
        if(rflows.length === 0) {
            return [env.endOfExecution(), [rexp]];
        }
        else {
            return [env.setFlowInfo(this.envExpressionCollapseStatmentFlows(rflows.map((ff) => ff.flowinfo))), [rexp]];
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
        this.raiseErrorIf(sinfo, env.isVarNameDefined(vname), `${vname} cannot shadow previous definition`);

        const vtype = (decltype instanceof AutoTypeSignature) ? infertype as ResolvedType : this.normalizeTypeOnly(decltype, env.binds);
        this.raiseErrorIf(sinfo, infertype.typeID !== vtype.typeID, `expression is not of (no conversion) declared type ${vtype.typeID}`);

        return env.addVar(vname, isConst, vtype, true, undefined);
    }

    private checkAssignSingleVariableFromTaskExplicit(sinfo: SourceInfo, env: StatementTypeEnvironment, vname: string, infertype: ResolvedType): StatementTypeEnvironment {
        const vinfo = env.lookupVar(vname);
        this.raiseErrorIf(sinfo, vinfo === null, `Variable ${vname} was not previously defined`);
        this.raiseErrorIf(sinfo, (vinfo as VarInfo).isConst, `Variable ${vname} is defined as const`);

        this.raiseErrorIf(sinfo, infertype.typeID !== (vinfo as VarInfo).declaredType.typeID, `expression is not of (no conversion) declared type ${(vinfo as VarInfo).declaredType.typeID}`);

        return env.setVar(vname, new FlowTypeInfoOption(infertype, FlowTypeTruthValue.Unknown, env.flowinfo));
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
        let eenv = env.setFlowInfo(this.envExpressionCollapseFlowInfos(this.envClearExps(env.createInitialEnvForExpressionEval(), svtrgt.name).flowinfo).expInferInfo);

        const rrtype = this.normalizeTypeOnly(ttask.task.mainfunc.invoke.resultType, TemplateBindScope.createBaseBindScope(ttask.binds));
        
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
        let eenv = env.setFlowInfo(this.envExpressionCollapseFlowInfos(this.envClearExps(env.createInitialEnvForExpressionEval(), svtrgt.name).flowinfo).expInferInfo);

        const rrtypebase = this.normalizeTypeOnly(ttask.task.mainfunc.invoke.resultType, TemplateBindScope.createBaseBindScope(ttask.binds));
        const rrtype = this.normalizeUnionList([rrtypebase, this.getSpecialNoneType()]);

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
        let eenv = env.setFlowInfo(this.envExpressionCollapseFlowInfos(this.envClearExps(env.createInitialEnvForExpressionEval(), svtrgt.name).flowinfo).expInferInfo);

        const rrtypebase = this.normalizeTypeOnly(ttask.task.mainfunc.invoke.resultType, TemplateBindScope.createBaseBindScope(ttask.binds));
        const rrtype = ResolvedType.createSingle(ResolvedListEntityAtomType.create(this.m_assembly.tryGetConceptTypeForFullyResolvedName("List") as EntityTypeDecl, rrtypebase));

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
        let eenv = env.setFlowInfo(this.envExpressionCollapseFlowInfos(this.envClearExps(env.createInitialEnvForExpressionEval(), svtrgt.name).flowinfo).expInferInfo);

        const rrtypebase = this.normalizeTypeOnly(ttask.task.mainfunc.invoke.resultType, TemplateBindScope.createBaseBindScope(ttask.binds));
        const rrtype = ResolvedType.createSingle(ResolvedTupleAtomType.create([this.getSpecialNatType(), rrtypebase]));

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

        const eenv = env.setFlowInfo(this.envExpressionCollapseFlowInfos(this.envClearExps(env.createInitialEnvForExpressionEval(), "self").flowinfo).expInferInfo);

        return [eenv, [tset]];
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
        this.gatherInfoTemplateTypesAndChecks(stmt.sinfo, env, tt, tmap);

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
        this.gatherInfoTemplateTypesAndChecks(stmt.sinfo, env, tt, tmap);

        this.raiseErrorIf(stmt.sinfo, stmt.args.length !== tmap.size, `number of expected args (${tmap.size}) and number provided (${stmt.args.length}) differ`);
        const args = stmt.args.map((arg, ii) => {
            this.raiseErrorIf(arg.sinfo, !tmap.has(ii), `Missing formatter for argument ${ii}`);
            const etype = tmap.get(ii) as ResolvedType;
            return this.emitCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), arg, etype), arg.sinfo, etype).expressionResult;
        });

        const cond = this.emitActionCallCoerceIfNeeded(this.checkExpression(env.createInitialEnvForExpressionEval(), stmt.cond, this.getSpecialBoolType()), stmt.cond.sinfo, this.getSpecialBoolType());

        return [env, [new TIRLoggerEmitConditionalStatement(stmt.sinfo, stmt.level, cond.expressionResult, stmt.msg, args)]];
    }

    private checkLoggerLevelStatement(env: StatementTypeEnvironment, stmt: LoggerLevelStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("LoggerLevelStatement");
    }

    private checkLoggerCategoryStatement(env: StatementTypeEnvironment, stmt: LoggerCategoryStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("LoggerCategoryStatement");
    }

    private checkLoggerPrefixStatement(env: StatementTypeEnvironment, stmt: LoggerPrefixStatement): [StatementTypeEnvironment, TIRStatement[]] {
        return TYPECHECKER_NOT_IMPLEMENTED<[StatementTypeEnvironment, TIRStatement[]]>("LoggerPrefixStatement");
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
        this.initializeForBody(srcFile, rtype, false, selfok);

        const evalue = this.emitCoerceIfNeeded(this.checkExpression(env, body, rtype), body.sinfo, rtype);
        const sblck = new TIRScopedBlockStatement([new TIRReturnStatement(body.sinfo, evalue.expressionResult)], true);

        return sblck.ops;
    }

    private checkBodyStatement(srcFile: string, env: StatementTypeEnvironment, body: ScopedBlockStatement, rtype: ResolvedType, taskok: boolean, selfok: "no" | "read" | "write"): TIRStatement[] {
        this.initializeForBody(srcFile, rtype, taskok, selfok);

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
                args.set("$" + ff.fname, new VarInfo(ff.ftype, true, false, true));
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
                args.set("$" + ff.fname, new VarInfo(ff.ftype, true, false, true));
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
            const args = new Map<string, VarInfo>().set("$value", new VarInfo(vtype, true, false, true));
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
        const args = new Map<string, VarInfo>().set("$value", new VarInfo(vtype, true, false, true));
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
            const args = new Map<string, VarInfo>().set("$value", new VarInfo(vtype, true, false, true));
            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgs(TemplateBindScope.createBaseBindScope(idp[2]), args);

            return idp[1].validates.map((inv) => {
                const iexp = this.emitCoerceIfNeeded(this.checkExpression(env.createFreshEnvExpressionFrom(), inv.exp.exp, this.getSpecialBoolType()), inv.exp.exp.sinfo, this.getSpecialBoolType());
                const vtype = this.toTIRTypeKey(idp[0]);

                return new TIRTypedeclInvariantDecl(iexp.expressionResult, vtype);
            });
        });
        
        return ([] as TIRTypedeclInvariantDecl[]).concat(...chkinvsaa);
    }

    private processPrecondition(invk: InvokeDecl, optthistype: ResolvedType | undefined, binds: TemplateBindScope, pcodes: Map<string, TIRCodePack>, exps: PreConditionDecl[]): TIRPreConditionDecl[] {
        try {
            let fargs = new Map<string, VarInfo>();
            let args: TIRFunctionParameter[] = [];

            if (optthistype !== undefined) {
                fargs.set("this", new VarInfo(optthistype, true, false, true));
                args.push(new TIRFunctionParameter("this", this.toTIRTypeKey(optthistype)));
            }

            invk.params.forEach((ff, fname) => {
                const ptype = this.normalizeTypeGeneral(ff.type, binds);
                if (ptype instanceof ResolvedFunctionType) {
                    args.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
                }
                else {
                    fargs.set(ff.name, new VarInfo(ptype, true, false, true));
                    args.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
                }
            });

            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgsPCodes(binds, pcodes, fargs);
            const clauses = exps
                .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
                .map((cev) => {
                    const exp = this.emitCoerceIfNeeded(this.checkExpression(env, cev.exp, this.getSpecialBoolType()), cev.exp.sinfo, this.getSpecialBoolType());

                    return new TIRPreConditionDecl(exp.expressionResult, args);
                });

            return clauses;
        }
        catch (ex) {
            return [];
        }
    }

    private processPostcondition(invk: InvokeDecl, optthistype: ResolvedType | undefined, binds: TemplateBindScope, pcodes: Map<string, TIRCodePack>, exps: PostConditionDecl[]): TIRPostConditionDecl[] {
        try {
            let fargs = new Map<string, VarInfo>();
            let args: TIRFunctionParameter[] = [];

            if (optthistype !== undefined) {
                fargs.set("this", new VarInfo(optthistype, true, false, true));
                args.push(new TIRFunctionParameter("this", this.toTIRTypeKey(optthistype)));
            }

            invk.params.forEach((ff, fname) => {
                const ptype = this.normalizeTypeGeneral(ff.type, binds);
                if (ptype instanceof ResolvedFunctionType) {
                    args.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
                }
                else {
                    fargs.set(ff.name, new VarInfo(ptype, true, false, true));
                    args.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
                }
            });

            if(optthistype !== undefined && invk.isThisRef) {
                fargs.set("$this", new VarInfo(optthistype, true, false, true));
                args.push(new TIRFunctionParameter("$this", this.toTIRTypeKey(optthistype)));
            }

            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgsPCodes(binds, pcodes, fargs);
            const clauses = exps
                .filter((cev) => isBuildLevelEnabled(cev.level, this.m_buildLevel))
                .map((cev) => {
                    const exp = this.emitCoerceIfNeeded(this.checkExpression(env, cev.exp, this.getSpecialBoolType()), cev.exp.sinfo, this.getSpecialBoolType());

                    return new TIRPostConditionDecl(exp.expressionResult, args);
                });

            return clauses;
        }
        catch (ex) {
            return [];
        }
    }

    processOOType(tkey: TIRTypeKey, rtype: ResolvedEntityAtomType, tdecl: OOPTypeDecl, binds: Map<string, ResolvedType>) {
        if (rtype instanceof ResolvedObjectEntityAtomType) {
            const tiroo = this.m_tirTypeMap.get(tkey) as TIRObjectEntityType;

            //set member fields
            tdecl.memberFields.forEach((mf) => {
                const fkey = TIRIDGenerator.generateMemberFieldID(tkey, mf.name);
                const decltype = this.toTIRTypeKey(this.normalizeTypeOnly(mf.declaredType, TemplateBindScope.createBaseBindScope(binds)));

                tiroo.memberFields.push(new TIRMemberFieldDecl(fkey, tkey, mf.name, mf.sourceLocation, mf.srcFile, mf.attributes, decltype));
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

    private checkInvokeDecl(sinfo: SourceInfo, invoke: InvokeDecl) {
        const allNames = new Set<string>();
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
        }
    }

    private checkPCodeDecl(sinfo: SourceInfo, fsig: ResolvedFunctionType) {
        const allNames = new Set<string>();
        for (let i = 0; i < fsig.params.length; ++i) {
            if (fsig.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(fsig.params[i].name), `Duplicate name in invocation signature paramaters "${fsig.params[i].name}"`);
                allNames.add(fsig.params[i].name);
            }
        
            const rtype = fsig.params[i].type;
            this.raiseErrorIf(sinfo, rtype instanceof ResolvedFunctionType, "Cannot have nested function type param");
        }
    }

    private processNamespaceFunctionInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, ibinds: Map<string, ResolvedType>, pcodes: Map<string, TIRCodePack>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...pcodes].some((pc) => pc[1].code.recursive === "yes"));

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                params.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, false, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)));
        const preconds = this.processPrecondition(invoke, undefined, TemplateBindScope.createBaseBindScope(ibinds), pcodes, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, undefined, TemplateBindScope.createBaseBindScope(ibinds), pcodes, invoke.postconditions);

        const env = StatementTypeEnvironment.createInitialEnvForStatementEval(TemplateBindScope.createBaseBindScope(ibinds), pcodes, new Set<string>(), fargs, []);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)), false, "no");
        return new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, false, false, false, false, params, false, restype, preconds, postconds, body);
    }

    private processNamespaceFunctionPrimitiveInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, ibinds: Map<string, ResolvedType>, pcodes: Map<string, TIRCodePack>): TIRInvokePrimitive {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...pcodes].some((pc) => pc[1].code.recursive === "yes"));

        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                params.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
            }
            else {
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)));
        const body = (invoke.body as BodyImplementation).body as string;
        return new TIRInvokePrimitive(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, params, restype, body);
    }

    private processNamespaceOperatorDeclInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl): TIRInvoke {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);
        this.raiseErrorIf(invoke.startSourceLocation, invoke.terms.length !== 0, "cannot have template parameters on operators");

        const recursive = invoke.recursive === "yes";

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeOnly(ff.type, TemplateBindScope.createEmptyBindScope());
            
            fargs.set(ff.name, new VarInfo(ptype, true, false, true));
            params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
        this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.length !== 0 || invoke.postconditions.length !== 0, "pre/post conditions not supported on operators yet");

        if(invoke.body === undefined) {
            return new TIRInvokeAbstractDeclaration(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, false, true, params, false, restype, [], []);
        }
        else {
            const env = StatementTypeEnvironment.createInitialEnvForStatementEval(TemplateBindScope.createEmptyBindScope(), new Map<string, TIRCodePack>(), new Set<string>(), fargs, []);
            const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()), false, "no");
            return new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, false, false, true, false, params, false, restype, [], [], body);
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
            fargs.set(ff.name, new VarInfo(ptype, true, false, true));
            params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
        this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.length !== 0 || invoke.postconditions.length !== 0, "pre/post conditions not supported on operators yet");

        const env = StatementTypeEnvironment.createInitialEnvForStatementEval(TemplateBindScope.createEmptyBindScope(), new Map<string, TIRCodePack>(), new Set<string>(), fargs, []);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()), false, "no");
        return new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, false, false, true, false, params, false, restype, [], [], body);
    }

    private processMemberFunctionInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, pcodes: Map<string, TIRCodePack>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...pcodes].some((pc) => pc[1].code.recursive === "yes"));

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                params.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, false, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, undefined, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, undefined, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, invoke.postconditions);

        const env = StatementTypeEnvironment.createInitialEnvForStatementEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, new Set<string>(), fargs, []);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, "no");
        return new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, false, false, false, false, params, false, restype, preconds, postconds, body);
    }

    private processMemberFunctionPrimitiveInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, pcodes: Map<string, TIRCodePack>): TIRInvokePrimitive {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...pcodes].some((pc) => pc[1].code.recursive === "yes"));

        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                params.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
            }
            else {
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));

        const body = (invoke.body as BodyImplementation).body as string;
        return new TIRInvokePrimitive(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, params, restype, body);
    }

    private processMemberMethodPureDeclInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, pcodes: Map<string, TIRCodePack>): TIRInvokeAbstractDeclaration {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...pcodes].some((pc) => pc[1].code.recursive === "yes"));

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                params.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, false, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        fargs.set("this", new VarInfo(enclosingdecl[0], true, false, true));

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, invoke.postconditions);

        return new TIRInvokeAbstractDeclaration(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, true, false, params, false, restype, preconds, postconds);
    }

    private processMemberMethodVirtualDeclInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, pcodes: Map<string, TIRCodePack>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...pcodes].some((pc) => pc[1].code.recursive === "yes"));

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                params.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, false, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        fargs.set("this", new VarInfo(enclosingdecl[0], true, false, true));

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, invoke.postconditions);

        const env = StatementTypeEnvironment.createInitialEnvForStatementEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, new Set<string>(), fargs, []);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, this.m_taskSelfOk);
        return new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, true, true, false, false, params, false, restype, preconds, postconds, body);
    }

    private processMemberMethodVirtualImplInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], declaredecl: [ResolvedType, InvokeDecl, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, pcodes: Map<string, TIRCodePack>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...pcodes].some((pc) => pc[1].code.recursive === "yes"));

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                params.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, false, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        fargs.set("this", new VarInfo(enclosingdecl[0], true, false, true));

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, declaredecl[1].preconditions.length !== 0 ? declaredecl[0] : enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, declaredecl[1].preconditions.length !== 0 ? declaredecl[1].preconditions : invoke.preconditions);
        const postconds = this.processPostcondition(invoke, declaredecl[1].postconditions.length !== 0 ? declaredecl[0] : enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, declaredecl[1].postconditions.length !== 0 ? declaredecl[1].postconditions : invoke.postconditions);

        const env = StatementTypeEnvironment.createInitialEnvForStatementEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, new Set<string>(), fargs, []);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, this.m_taskSelfOk);
        return new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, true, true, false, false, params, false, restype, preconds, postconds, body);
    }

    private processMemberMethodImplInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, pcodes: Map<string, TIRCodePack>): TIRInvokeImplementation {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && [...pcodes].some((pc) => pc[1].code.recursive === "yes"));

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeGeneral(ff.type, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds));
            if (ptype instanceof ResolvedFunctionType) {
                params.push(new TIRFunctionParameter(ff.name, (pcodes.get(ff.name) as TIRCodePack).ftype.tkey));
            }
            else {
                fargs.set(ff.name, new VarInfo(ptype, true, false, true));
                params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype)));
            }
        });

        fargs.set("this", new VarInfo(enclosingdecl[0], true, false, true));
        
        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const preconds = this.processPrecondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, enclosingdecl[0], TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, invoke.postconditions);

        const env = StatementTypeEnvironment.createInitialEnvForStatementEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), pcodes, new Set<string>(), fargs, []);
        const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), this.m_taskOpsOk, this.m_taskSelfOk);
        return new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, true, false, false, false, params, invoke.isThisRef, restype, preconds, postconds, body);
    }

    private processPCodeInvokeInfo(name: string, invkey: TIRInvokeKey, enclosingDecl: [ResolvedType, TIRType, OOPTypeDecl, Map<string, ResolvedType>] | undefined, kind: "namespace" | "static" | "member" | "operator", invoke: InvokeDecl, ibinds: Map<string, ResolvedType>, pcodes: PCode[], pargs: [string, ResolvedType][]): MIRInvokeDecl {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);

        xxxx;
    }

    private ensureTIRNamespaceDecl(ns: string): TIRNamespaceDeclaration {
        if(!this.m_tirNamespaceMap.has(ns)) {
            this.m_tirNamespaceMap.set(ns, new TIRNamespaceDeclaration(ns));
        }

        return this.m_tirNamespaceMap.get(ns) as TIRNamespaceDeclaration;
    }

    processConstExpr(cdcl: NamespaceConstDecl) {
        try {
            this.m_file = cdcl.srcFile;
            this.m_rtype = this.getSpecialNoneType();
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;

            const decltype = this.normalizeTypeOnly(cdcl.declaredType, TemplateBindScope.createEmptyBindScope());
            const tirdecltype = this.toTIRTypeKey(decltype);

            this.raiseErrorIf(cdcl.value.exp.sinfo, cdcl.value.captured.size !== 0, "cannot have unbound variables in namespace const expression");
            const declvalue = this.emitCoerceIfNeeded(this.checkExpression(ExpressionTypeEnvironment.createInitialEnvForEvalStandalone(TemplateBindScope.createEmptyBindScope()), cdcl.value.exp, decltype), cdcl.value.exp.sinfo, decltype);

            const tridecl = new TIRNamespaceConstDecl(cdcl.ns, cdcl.name, cdcl.sourceLocation, cdcl.srcFile, cdcl.attributes, tirdecltype, declvalue.expressionResult);

            const tirns = this.ensureTIRNamespaceDecl(cdcl.ns);
            tirns.consts.set(cdcl.name, tridecl);
        }
        catch (ex) {
            ;
        }
    }

    processNamespaceFunctionDecl(fkey: TIRInvokeKey, ns: string, name: string, invoke: InvokeDecl, binds: Map<string, ResolvedType>, terms: TIRTypeKey[], pcodes: Map<string, TIRCodePack>) {
        try {
            this.m_file = invoke.srcFile;
            this.m_rtype = this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(binds));
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;

            let iinv: TIRInvoke | undefined = undefined;
            if(typeof((invoke.body as BodyImplementation).body) === "string") {
                iinv = this.processNamespaceFunctionPrimitiveInvokeInfo(name, fkey, invoke, binds, pcodes);
            }
            else {
                iinv = this.processNamespaceFunctionInvokeInfo(name, fkey, invoke, binds, pcodes);
            }

            const tirns = this.ensureTIRNamespaceDecl(ns);
            tirns.functions.set(name, new TIRNamespaceFunctionDecl(ns, invoke.startSourceLocation, invoke.srcFile, iinv, terms));
        }
        catch (ex) {
           ;
        }
    }

    processNamespaceOperatorDecl(fkey: TIRInvokeKey, ns: string, name: string, invoke: InvokeDecl) {
        try {
            this.m_file = invoke.srcFile;
            this.m_rtype = this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope());
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;

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

    processNamespaceOperatorImpl(fkey: TIRInvokeKey, ns: string, name: string, invoke: InvokeDecl) {
        try {
            this.m_file = invoke.srcFile;
            this.m_rtype = this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope());
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;

            const iinv = this.processNamespaceOperatorImplInvokeInfo(name, fkey, invoke);

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

    processMemberConst(decl: [ResolvedType, OOPTypeDecl, StaticMemberDecl, Map<string, ResolvedType>]) {
        try {
            this.m_file = decl[2].srcFile;
            this.m_rtype = this.getSpecialNoneType();
            this.m_taskOpsOk = false;
            this.m_taskSelfOk = "no";
            this.m_taskType = undefined;

            const tirtypetry = this.m_tirTypeMap.get(decl[0].typeID);
            this.raiseErrorIf(decl[2].sourceLocation, tirtypetry === undefined || !(tirtypetry instanceof TIROOType), "internal error const member -- failed to register type first");
            const tirtype = tirtypetry as TIROOType;

            const decltype = this.normalizeTypeOnly(decl[2].declaredType, TemplateBindScope.createBaseBindScope(decl[3]));
            const tirdecltype = this.toTIRTypeKey(decltype);

            this.raiseErrorIf(decl[2].value.exp.sinfo, decl[2].value.captured.size !== 0, "cannot have unbound variables in namespace const expression");
            const declvalue = this.emitCoerceIfNeeded(this.checkExpression(ExpressionTypeEnvironment.createInitialEnvForEvalStandalone(TemplateBindScope.createBaseBindScope(decl[3])), decl[2].value.exp, decltype), decl[2].value.exp.sinfo, decltype);

            tirtype.constMembers.push(new TIRConstMemberDecl(tirtype.tkey, decl[2].name, decl[2].sourceLocation, decl[2].srcFile, decl[2].attributes, tirdecltype, declvalue.expressionResult));
        }
        catch(ex) {
            ;
        }
    }

    processMemberFunction(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
    }

    processMemberMethodVirtual(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
    }

    processMemberMethodOverride(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
    }

    processMemberMethodDirect(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
    }

    processMemberTaskMethod(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
    }

    processMemberTaskAction(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
    }

    processMemberTaskMain(vkey: MIRVirtualMethodKey, mkey: MIRInvokeKey, shortname: string, name: string, enclosingDecl: [MIRType, OOPTypeDecl, Map<string, ResolvedType>], mdecl: MemberMethodDecl, binds: Map<string, ResolvedType>, pcodes: PCode[], cargs: [string, ResolvedType][]) {
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
