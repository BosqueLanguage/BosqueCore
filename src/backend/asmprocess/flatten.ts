import { DashResultTypeSignature, EListTypeSignature, FormatPathTypeSignature, FormatStringTypeSignature, FullyQualifiedNamespace, LambdaParameterPackTypeSignature, NominalTypeSignature, TypeSignature, VoidTypeSignature } from "../../frontend/type";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, AgentInvokeExpression, APIInvokeExpression, AssertStatement, BaseRValueExpression, BinAddExpression, BinDivExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallRefVariableExpression, CallTaskActionExpression, CallTypeFunctionExpression, ChkLogicBaseExpression, ChkLogicExpression, ChkLogicExpressionTag, ChkLogicImpliesExpression, ConditionalValueExpression, DebugStatement, DispatchPatternStatement, DispatchTaskStatement, EmptyStatement, Expression, ExpressionBodyImplementation, ExpressionTag, FormatStringArgComponent, FormatStringTextComponent, HoleBodyImplementation, HoleStatement, IfElifElseStatement, IfElseStatement, IfStatement, ITestGuard, ITestGuardSet, ITestSimpleGuard, LambdaInvokeExpression, LiteralCStringExpression, LiteralFormatCStringExpression, LiteralFormatStringExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralStringExpression, LiteralTypedCStringExpression, LiteralTypeDeclValueExpression, LiteralTypedFormatCStringExpression, LiteralTypedFormatStringExpression, LiteralTypedStringExpression, LogicAndExpression, LogicOrExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, PostfixOp, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, RValueExpression, RValueExpressionTag, SelfUpdateStatement, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, TaskAccessInfoExpression, TaskAllExpression, TaskCheckAndHandleTerminationStatement, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VarUpdateStatement, VoidRefCallStatement } from "../../frontend/body";
import { Assembly, PreConditionDecl, TypedeclTypeDecl } from "../../frontend/assembly";

import { IRDashResultTypeSignature, IREListTypeSignature, IRFormatCStringTypeSignature, IRFormatPathFragmentTypeSignature, IRFormatPathGlobTypeSignature, IRFormatPathTypeSignature, IRFormatStringTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature, IRVoidTypeSignature } from "../irdefs/irtype";
import { DateRepresentation, DeltaDateRepresentation, DeltaTimeRepresentation, IRLiteralChkIntExpression, IRLiteralChkNatExpression, IRLiteralBoolExpression, IRLiteralByteBufferExpression, IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralComplexExpression, IRLiteralCRegexExpression, IRLiteralCStringExpression, IRLiteralDecimalExpression, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaLogicalTimeExpression, IRLiteralDeltaSecondsExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralISOTimeStampExpression, IRLiteralLatLongCoordinateExpression, IRLiteralLogicalTimeExpression, IRLiteralNatExpression, IRLiteralNoneExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralRationalExpression, IRLiteralSHAContentHashExpression, IRLiteralStringExpression, IRLiteralTAITimeExpression, IRLiteralTZDateTimeExpression, IRLiteralUnicodeCharExpression, IRLiteralUnicodeRegexExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRStatement, TimeRepresentation, IRLiteralFormatStringExpression, IRFormatStringTextComponent, IRFormatStringArgComponent, IRFormatStringComponent, IRLiteralFormatCStringExpression, IRLiteralTypedExpression, IRLiteralExpression, IRTypeDeclInvariantCheckStatement, IRLiteralTypedStringExpression, IRLiteralTypedCStringExpression, IRLiteralTypedFormatStringExpression, IRLiteralTypedFormatCStringExpression, IRTaskAccessIDExpression, IRTaskAccessParentIDExpression, IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression, IRAccessNamespaceConstantExpression, IRAccessStaticFieldExpression, IRAccessEnumExpression, IRSimpleExpression, IRPreconditionCheckStatement, IRExpression, IRTempAssignExpressionStatement, IRAccessTempVariableExpression, IRAccessLocalVariableExpression, IRAccessCapturedVariableExpression, IRAccessParameterVariableExpression, IRPrefixNotOpExpression, IRAccessTypeDeclValueExpression, IRConstructSafeTypeDeclExpression, IRPrefixNegateOpExpression, IRBinAddExpression, IRErrorAdditionBoundsCheckStatement, IRBinSubExpression, IRBinMultExpression, IRBinDivExpression, IRErrorDivisionByZeroCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRNumericEqExpression, IRNumericNeqExpression, IRNumericLessExpression, IRNumericLessEqExpression, IRNumericGreaterExpression, IRNumericGreaterEqExpression, IRLogicAndExpression, IRLogicOrExpression, IRNopStatement, IRVariableDeclarationStatement, IRVariableInitializationStatement, IRReturnVoidSimpleStatement, IRAbortStatement, IRImmediateExpression, IRReturnSimpleStatement, IRReturnValueSimpleStatement, IRBlockStatement, IRChkLogicImpliesShortCircuitStatement, IRInvokeDirectExpression, IRLogicSimpleConditionalExpression, IRLogicConditionalStatement, IRVariableInitializationDirectInvokeStatement, IRInvokeSimpleExpression, IRInvokeImplicitsExpression, IRTempAssignStdInvokeStatement, IRTempAssignRefInvokeStatement, IRReturnDirectInvokeStatement, IRAssertStatement, IRValidateStatement, IRDebugStatement, IRInvokeExpression } from "../irdefs/irbody";
import { IRRegex } from "../irdefs/irsupport";
import {} from "../irdefs/irassembly";

import assert from "node:assert";
import { SourceInfo } from "../../frontend/build_decls";

class ASMToIRConverter {
    readonly assembly: Assembly;

    regexs: IRRegex[];
    errCtr: number;

    currentFile: string | undefined;

    isTaskAllowed: boolean = false;
    currentReturnType: IRTypeSignature | undefined;
    currentImplicitReturnVar: string | undefined;

    pendingblocks: IRStatement[][];
    rescopeStack: Map<string, string>[]; //Maps from old name to new name
    tmpVarCtr: number;

    constructor(assembly: Assembly) {
        this.assembly = assembly;
        
        this.regexs = [];
        this.errCtr = 0;

        this.pendingblocks = [];
        this.rescopeStack = [];
        this.tmpVarCtr = 0;
    }

    private generateTempVarName(): string {
        const vname = `tmp_${this.tmpVarCtr}`;
        this.tmpVarCtr += 1;
        return vname;
    }

    private processLocalVariableName(vname: string): string {
        for(let i = this.rescopeStack.length - 1; i >= 0; --i) {
            const rescopeMap = this.rescopeStack[i];
            if(rescopeMap.has(vname)) {
                return rescopeMap.get(vname) as string;
            }
        }

        return vname;
    }

    private pushStatementBlock() {
        this.pendingblocks.push([]);
    }

    private popStatementBlock(): IRStatement[] {
        return this.pendingblocks.pop() as IRStatement[];
    }

    private pushStatement(stmt: IRStatement) {
        return this.pendingblocks[this.pendingblocks.length - 1].push(stmt);
    }

    private pushStatements(stmts: IRStatement[]) {
        return this.pendingblocks[this.pendingblocks.length - 1].push(...stmts);
    }

    private static extractLiteralDateInfo(datestr: string): DateRepresentation {
        const y = parseInt(datestr.slice(0, 4), 10);
        const m = parseInt(datestr.slice(5, 7), 10);
        const d = parseInt(datestr.slice(8, 10), 10);

        return new DateRepresentation(y, m, d);
    }

    private static extractLiteralTimeInfo(timestr: string): TimeRepresentation {
        const h = parseInt(timestr.slice(0, 2), 10);
        const m = parseInt(timestr.slice(3, 5), 10);
        const s = parseInt(timestr.slice(6, 8), 10);
        
        return new TimeRepresentation(h, m, s);
    }

    private static extractLiteralDeltaDateInfo(datestr: string): DeltaDateRepresentation {
        const pa = datestr.split("-");
        const y = parseInt(pa[0], 10);
        const m = parseInt(pa[1], 10);
        const d = parseInt(pa[2], 10);

        return new DeltaDateRepresentation(y, m, d);
    }

    private static extractLiteralDeltaTimeInfo(datestr: string): DeltaTimeRepresentation {
        const pa = datestr.split(":");
        const h = parseInt(pa[0], 10);
        const m = parseInt(pa[1], 10);
        const s = parseInt(pa[2], 10);

        return new DeltaTimeRepresentation(h, m, s);
    }

    private processRegex(inns: FullyQualifiedNamespace, regexstr: string): IRRegex {
        const rectr = this.regexs.length;
        
        const inst: IRRegex = new IRRegex(rectr); //TODO: need to make the real regex here
        this.regexs.push(inst);

        assert(false, "ASMToIRConverter::processRegex - Regex processing not yet implemented");
        //return inst;
    }

    private processStringBytes(sval: string): number[] {
        const bbuff = Buffer.from(sval, "utf8");
        let bytes: number[] = [];
        for(let i = 0; i < bbuff.length; ++i) {
            bytes.push(bbuff[i]);
        }

        return bytes;
    }

    private processTypeSignature(tsig: TypeSignature): IRTypeSignature {
        if(tsig instanceof VoidTypeSignature) {
            return new IRVoidTypeSignature();
        }
        else if(tsig instanceof NominalTypeSignature) {
            return new IRNominalTypeSignature(tsig.tkeystr);
        }
        else if(tsig instanceof EListTypeSignature) {
            const elisttsig = tsig as EListTypeSignature;
            const irents = elisttsig.entries.map<IRTypeSignature>((ent) => this.processTypeSignature(ent));

            return new IREListTypeSignature(tsig.tkeystr, irents);
        }
        else if(tsig instanceof DashResultTypeSignature) {
            const drtsig = tsig as DashResultTypeSignature;
            const irents = drtsig.entries.map<IRTypeSignature>((ent) => this.processTypeSignature(ent));

            return new IRDashResultTypeSignature(tsig.tkeystr, irents);
        }
        else if(tsig instanceof FormatStringTypeSignature) {
            const ffmtsig = tsig as FormatStringTypeSignature;
            const irfmts = ffmtsig.terms.map<{argname: string, argtype: IRTypeSignature}>((term) => {
                return {argname: term.argname, argtype: this.processTypeSignature(term.argtype)};
            });

            if(ffmtsig.oftype === "CString") {
                return new IRFormatCStringTypeSignature(tsig.tkeystr, this.processTypeSignature(ffmtsig.rtype), irfmts);
            }
            else {
                return new IRFormatStringTypeSignature(tsig.tkeystr, this.processTypeSignature(ffmtsig.rtype), irfmts);
            }
        }
        else if(tsig instanceof FormatPathTypeSignature) {
            const fpathtsig = tsig as FormatPathTypeSignature;
            const irfmts = fpathtsig.terms.map<{argname: string, argtype: IRTypeSignature}>((term) => {
                return {argname: term.argname, argtype: this.processTypeSignature(term.argtype)};
            });

            if(fpathtsig.oftype === "Path") {
                return new IRFormatPathTypeSignature(tsig.tkeystr, this.processTypeSignature(fpathtsig.rtype), irfmts);
            }
            else if(fpathtsig.oftype === "PathFragment") {
                return new IRFormatPathFragmentTypeSignature(tsig.tkeystr, this.processTypeSignature(fpathtsig.rtype), irfmts);
            }
            else {
                return new IRFormatPathGlobTypeSignature(tsig.tkeystr, this.processTypeSignature(fpathtsig.rtype), irfmts);
            }
        }
        else if(tsig instanceof LambdaParameterPackTypeSignature) {
            const lppsig = tsig as LambdaParameterPackTypeSignature;

            const stdvals = lppsig.stdvalues.map<{vname: string, vtype: IRTypeSignature}>((sv) => {
                return {vname: sv.vname, vtype: this.processTypeSignature(sv.vtype)};
            });
            const lambdavals = lppsig.lambdavalues.map<{lname: string, ltype: IRLambdaParameterPackTypeSignature}>((lv) => {
                return {lname: lv.lname, ltype: this.processTypeSignature(lv.ltype) as IRLambdaParameterPackTypeSignature};
            });

            return new IRLambdaParameterPackTypeSignature(tsig.tkeystr, stdvals, lambdavals);
        }
        else {
            assert(false, `ASMToIRConverter: Unsupported type signature -- ${tsig.tkeystr}`);
        }
    }

    //If we flatten an expression but it is nested then we need to simplify it -- this handles that by creating temps!
    private makeExpressionSimple(exp: IRExpression, oftype: TypeSignature): IRSimpleExpression {
        if(exp instanceof IRSimpleExpression) {
            return exp;
        }
        else {
            const irtype = this.processTypeSignature(oftype);
            const tmpname = this.generateTempVarName();

            if(exp instanceof IRInvokeSimpleExpression) {
                this.pushStatement(new IRTempAssignStdInvokeStatement(tmpname, exp, irtype));
            }
            else if(exp instanceof IRInvokeImplicitsExpression) {
                this.pushStatement(new IRTempAssignRefInvokeStatement(tmpname, irtype, exp.ivar, exp.ivartype, exp.passkind, exp));
            }
            else {
                this.pushStatement(new IRTempAssignExpressionStatement(tmpname, exp, irtype));
            }

             return new IRAccessTempVariableExpression(tmpname);
        }
    }

    private coerceToBoolForTest(exp: IRSimpleExpression, oftype: TypeSignature): IRSimpleExpression {
        if(oftype.tkeystr === "Bool") {
            return exp;
        }
        else {
            return new IRAccessTypeDeclValueExpression(this.processTypeSignature(oftype), exp);
        }
    }

    private makeCoercionExplicitAsNeeded(exp: IRSimpleExpression, fromtype: TypeSignature, totype: TypeSignature): IRSimpleExpression {
        if(fromtype.tkeystr === totype.tkeystr) {
            return exp;
        }
        else {
            assert(false, "ASMToIRConverter::makeCoercionExplicit - Not Implemented");
        }
    }

    private static isLiteralFalseExpression(exp: IRExpression): boolean {
        return exp instanceof IRLiteralBoolExpression && exp.value === false;
    }

    private static isLiteralTrueExpression(exp: IRExpression): boolean {
        return exp instanceof IRLiteralBoolExpression && exp.value === true;
    }

    private getSpecialType(sinfo: SourceInfo, tname: string): TypeSignature {
        const coredecl = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === tname);
        assert(coredecl !== undefined, `ASMToIRConverter::getSpecialType - Missing core type declaration for ${tname}`);
        return new NominalTypeSignature(sinfo, undefined, coredecl, []);
    }

    /*
    private processITest_None(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!none === some
        if(isnot) {
            const rinfo = this.relations.splitOnSome(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to some-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapSomeT, bindfalse: rinfo.hasnone ? this.getWellKnownType("None") : undefined };
            }
        }
        else {
            const rinfo = this.relations.splitOnNone(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to none-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.hasnone ? this.getWellKnownType("None") : undefined, bindfalse: rinfo.remainSomeT };
            }
        }
    }

    private processITest_Some(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!some === none
        if(isnot) {
            const rinfo = this.relations.splitOnNone(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to none-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.hasnone ? this.getWellKnownType("None") : undefined, bindfalse: rinfo.remainSomeT };
            }
        }
        else {
            const rinfo = this.relations.splitOnSome(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to some-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapSomeT, bindfalse: rinfo.hasnone ? this.getWellKnownType("None") : undefined };
            }
        }
    }

    private processITest_Ok(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!ok === err
        if(isnot) {
            const rinfo = this.relations.splitOnErr(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to err-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapErrE, bindfalse: rinfo.remainOkT };
            }
        }
        else {
            const rinfo = this.relations.splitOnOk(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to nothing-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapOkT, bindfalse: rinfo.remainErrE };
            }
        }
    }

    private processITest_Err(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        //!err === ok
        if(isnot) {
            const rinfo = this.relations.splitOnOk(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to err-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapOkT, bindfalse: rinfo.remainErrE };
            }
        }
        else {
            const rinfo = this.relations.splitOnErr(src, this.constraints);
            if(rinfo === undefined) {
                this.reportError(src.sinfo, `Unable to nothing-split type ${src.emit()}`);
                return { bindtrue: undefined, bindfalse: undefined };
            }
            else {
                return { bindtrue: rinfo.overlapErrE, bindfalse: rinfo.remainOkT };
            }
        }
    }

    private processITest_Error(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Rejected(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Denied(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Flagged(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Success(src: TypeSignature, isnot: boolean): { bindtrue: TypeSignature | undefined, bindfalse: TypeSignature | undefined } {
        xxxx;
    }

    private processITest_Type(src: TypeSignature, oftype: TypeSignature): { ttrue: TypeSignature[], tfalse: TypeSignature[] } {
        const rinfo = this.relations.refineType(src, oftype, this.constraints);
        if(rinfo === undefined) {
            this.reportError(src.sinfo, `Unable to some-split type ${src.emit()}`);
            return { ttrue: [], tfalse: [] };
        }
        else {
            return { ttrue: rinfo.overlap, tfalse: rinfo.remain };
        }
    }
    
    private processITestAsBoolean(sinfo: SourceInfo, env: TypeEnvironment, src: TypeSignature, tt: ITest): { ttrue: boolean, tfalse: boolean } {
        if(tt instanceof ITestType) {
            if(!this.checkTypeSignature(tt.ttype)) {
                return { ttrue: false, tfalse: false };
            }
            else {
                const tres = this.processITest_Type(src, tt.ttype);
                if(tt.isnot) {
                    return { ttrue: tres.tfalse.length !== 0, tfalse: tres.ttrue.length !== 0 };
                }
                else {
                    return { ttrue: tres.ttrue.length !== 0, tfalse: tres.tfalse.length !== 0 };
                }
            }
        }
        else {
            if(tt instanceof ITestNone) {
                const tres = this.processITest_None(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestSome) {
                const tres = this.processITest_Some(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestOk) {
                const tres = this.processITest_Ok(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestError) {
                const tres = this.processITest_Error(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestRejected) {
                const tres = this.processITest_Rejected(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestDenied) {
                const tres = this.processITest_Denied(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestFlagged) {
                const tres = this.processITest_Flagged(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else if(tt instanceof ITestSuccess) {
                const tres = this.processITest_Success(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
            else {
                assert(tt instanceof ITestFail, "missing case in ITest");
                const tres = this.processITest_Err(src, tt.isnot);
                return { ttrue: tres.bindtrue !== undefined, tfalse: tres.bindfalse !== undefined };
            }
        }
    }

    private processITestConvertLUB(sinfo: SourceInfo, opts: TypeSignature[], lubtype: TypeSignature): TypeSignature | undefined {
        const flowlub = this.relations.flowTypeLUB(sinfo, lubtype, opts, this.constraints);
        if(flowlub instanceof ErrorTypeSignature) {
            return lubtype;
        }
        else {
            return flowlub;
        }
    }

    private processITestAsConvert(sinfo: SourceInfo, env: TypeEnvironment, src: TypeSignature, tt: ITest): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        if(tt instanceof ITestType) {
            if(!this.checkTypeSignature(tt.ttype)) {
                return { ttrue: undefined, tfalse: undefined };
            }
            else {
                const tres = this.processITest_Type(src, tt.ttype);
                if(tt.isnot) {
                    const ttrue = tres.tfalse.length !== 0 ? this.processITestConvertLUB(sinfo, tres.tfalse, src) : undefined; //negate takes the remain and lubs to the src
                    const tfalse = tres.ttrue.length !== 0 ? tt.ttype : undefined; //overlap and passes as the user spec type -- does not matter now but short circuiting return will use this

                    return { ttrue: ttrue, tfalse: tfalse };
                }
                else {
                    const ttrue = tres.ttrue.length !== 0 ? tt.ttype : undefined; //always cast to what the user asked for
                    const tfalse = tres.tfalse.length !== 0 ? this.processITestConvertLUB(sinfo, tres.tfalse, src) : undefined; //cast to the LUB of the remaining types (with src as a default option)

                    return { ttrue: ttrue, tfalse: tfalse };
                }
            }
        }
        else {
            if(tt instanceof ITestNone) {
                const tres = this.processITest_None(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestSome) {
                const tres = this.processITest_Some(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestOk) {
                const tres = this.processITest_Ok(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestError) {
                const tres = this.processITest_Error(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestRejected) {
                const tres = this.processITest_Rejected(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestDenied) {
                const tres = this.processITest_Denied(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestFlagged) {
                const tres = this.processITest_Flagged(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else if(tt instanceof ITestSuccess) {
                const tres = this.processITest_Success(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
            else {
                assert(tt instanceof ITestFail, "missing case in ITest");
                const tres = this.processITest_Err(src, tt.isnot);
                return { ttrue: tres.bindtrue, tfalse: tres.bindfalse };
            }
        }
    }
    */
    
    private flattenITestGuardExpression(exp: Expression): IRSimpleExpression {
        switch (exp.tag) {
            case ExpressionTag.CallRefVariableExpression: {
                const crexp = exp as CallRefVariableExpression;

                return this.coerceToBoolForTest(this.flattenCallRefVariableExpression(crexp), crexp.getType());
            }
            case ExpressionTag.CallRefThisExpression: {
                const crexp = exp as CallRefThisExpression;
                
                return this.coerceToBoolForTest(this.flattenCallRefThisExpression(crexp), crexp.getType());
            }
            case ExpressionTag.CallRefSelfExpression: {
                const crexp = exp as CallRefSelfExpression;

                return this.coerceToBoolForTest(this.flattenCallRefSelfExpression(crexp), crexp.getType());
            }
            case ExpressionTag.CallTaskActionExpression: {
                const crexp = exp as CallTaskActionExpression;
                
                return this.coerceToBoolForTest(this.flattenCallTaskActionExpression(crexp), crexp.getType());
            }
            default: {
                const ttag = exp.tag;

                if(ttag === ExpressionTag.CallNamespaceFunctionExpression) {
                    const crexp = exp as CallNamespaceFunctionExpression;

                    return this.coerceToBoolForTest(this.flattenCallNamespaceFunctionExpression(crexp), crexp.getType());
                }
                else if(ttag === ExpressionTag.CallTypeFunctionExpression) {
                    const crexp = exp as CallTypeFunctionExpression;

                    return this.coerceToBoolForTest(this.flattenCallTypeFunctionExpression(crexp), crexp.getType());
                }
                else if(ttag === ExpressionTag.LambdaInvokeExpression) {
                    const crexp = exp as LambdaInvokeExpression;

                    return this.coerceToBoolForTest(this.flattenLambdaInvokeExpression(crexp), crexp.getType());
                }
                else if(ttag === ExpressionTag.PostfixOpExpression) {
                    const crexp = exp as PostfixOp;

                    return this.coerceToBoolForTest(this.flattenPostfixOp(crexp), crexp.getType());
                }
                else if(ttag === ExpressionTag.PrefixNotOpExpression) {
                    const nexp = exp as PrefixNotOpExpression;
                    const nval = this.coerceToBoolForTest(this.flattenITestGuardExpression(nexp.exp), nexp.exp.getType());

                    return new IRPrefixNotOpExpression(nval, this.getSpecialType(exp.sinfo, "Bool"));
                }
                else if(ttag === ExpressionTag.LogicAndExpression) {
                    const aexps = (exp as LogicAndExpression).exps.map((e) => this.coerceToBoolForTest(this.flattenITestGuardExpression(e), e.getType()));
                    
                    const mustfalse = aexps.some((aexp) => ASMToIRConverter.isLiteralFalseExpression(aexp));
                    if(mustfalse) {
                        return new IRLiteralBoolExpression(false);
                    }
                    else {
                        const filteredexps = aexps.filter((aexp) => !ASMToIRConverter.isLiteralTrueExpression(aexp));
                        if(filteredexps.length === 0) {
                            return new IRLiteralBoolExpression(true);
                        }
                        else if(filteredexps.length === 1) {
                            return filteredexps[0];
                        }
                        else {
                            return new IRLogicAndExpression(filteredexps);
                        }
                    }
                }
                else {
                    return this.coerceToBoolForTest(this.flattenExpression(exp), exp.getType());
                }
            }
        }
    }

    private flattenITestGuard(sinfo: SourceInfo, tt: ITestGuard, gidx: number): [IRSimpleExpression, { ee: IRImmediateExpression, gidx: number } | undefined] {
        if(tt instanceof ITestSimpleGuard) {
            return [this.flattenITestGuardExpression(tt.exp), undefined];
        }
        else {
            assert(false, "Unknown ITestGuard type"); //TODO check and do binders here!!!
        }
    }

    private flattenITestGuardSet(sinfo: SourceInfo, tt: ITestGuardSet): [IRSimpleExpression, { ee: IRImmediateExpression, gidx: number }[]] {
        const grenvs = tt.guards.map((guard, ii) => this.flattenITestGuard(sinfo, guard, ii));
        const iebinds = grenvs.map((ginfo) => ginfo[1]).filter((gbi) => gbi !== undefined) as { ee: IRImmediateExpression, gidx: number }[];

        const mustfalse = grenvs.some((aexp) => ASMToIRConverter.isLiteralFalseExpression(aexp[0]));
        if(mustfalse) {
            return [new IRLiteralBoolExpression(false), iebinds];
        }
        else {
            const filteredexps = grenvs.filter((aexp) => !ASMToIRConverter.isLiteralTrueExpression(aexp[0]));
            if(filteredexps.length === 0) {
                return [new IRLiteralBoolExpression(true), iebinds];
            }
            else if(filteredexps.length === 1) {
                return [filteredexps[0][0], iebinds];
            }
            else {
                return [new IRLogicAndExpression(filteredexps.map((fe) => fe[0])), iebinds];
            }
        }
    }

    private flattenCallNamespaceFunctionExpression(exp: CallNamespaceFunctionExpression): IRExpression {
        assert(false, "ASMToIRConverter::flattenCallNamespaceFunctionExpression - Not Implemented");
    }

    private flattenCallTypeFunctionExpression(exp: CallTypeFunctionExpression): IRExpression {
        assert(false, "ASMToIRConverter::flattenCallTypeFunctionExpression - Not Implemented");
    }

    private flattenLambdaInvokeExpression(exp: LambdaInvokeExpression): IRExpression {
        assert(false, "ASMToIRConverter::flattenLambdaInvokeExpression - Not Implemented");
    }

    private flattenPostfixOp(exp: PostfixOp): IRExpression {
        assert(false, "ASMToIRConverter::flattenPostfixOp - Not Implemented");
    }

    private unwrapBinArgs(left: IRExpression, right: IRExpression, lefttype: TypeSignature, righttype: TypeSignature): [IRSimpleExpression, IRSimpleExpression] {
        const lsimp = this.makeExpressionSimple(left, lefttype);
        const rsimp = this.makeExpressionSimple(right, righttype);
        
        const lres = ((lefttype instanceof NominalTypeSignature) && (lefttype.decl instanceof TypedeclTypeDecl)) ? new IRAccessTypeDeclValueExpression(this.processTypeSignature(lefttype), lsimp) : lsimp;
        const rres = ((righttype instanceof NominalTypeSignature) && (righttype.decl instanceof TypedeclTypeDecl)) ? new IRAccessTypeDeclValueExpression(this.processTypeSignature(righttype), rsimp) : rsimp;

        return [lres, rres];
    }

    private flattenExpression(exp: Expression): IRExpression {
        const ttag = exp.tag;

        if(ttag === ExpressionTag.LiteralNoneExpression) {
            return new IRLiteralNoneExpression();
        }
        else if(ttag === ExpressionTag.LiteralBoolExpression) {
            return new IRLiteralBoolExpression((exp as LiteralSimpleExpression).value === "true");
        }
        else if(ttag === ExpressionTag.LiteralNatExpression) {
            return new IRLiteralNatExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralIntExpression) {
            return new IRLiteralIntExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralChkNatExpression) {
            return new IRLiteralChkNatExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralChkIntExpression) {
            return new IRLiteralChkIntExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralRationalExpression) {
            const rrval = (exp as LiteralSimpleExpression).value;
            const slpos = rrval.indexOf("/");
            
            return new IRLiteralRationalExpression(rrval.slice(0, slpos), rrval.slice(slpos + 1, -1));
        }
        else if(ttag === ExpressionTag.LiteralFloatExpression) {
            return new IRLiteralFloatExpression((exp as LiteralSimpleExpression).value);
        }
        else if(ttag === ExpressionTag.LiteralDecimalExpression) {
            return new IRLiteralDecimalExpression((exp as LiteralSimpleExpression).value);
        }
        else if(ttag === ExpressionTag.LiteralDecimalDegreeExpression) {
            return new IRLiteralDecimalExpression((exp as LiteralSimpleExpression).value.slice(0, -2));
        }
        else if(ttag === ExpressionTag.LiteralLatLongCoordinateExpression) {
            const latsplit = (exp as LiteralSimpleExpression).value.indexOf("lat");
            return new IRLiteralLatLongCoordinateExpression((exp as LiteralSimpleExpression).value.slice(0, latsplit), (exp as LiteralSimpleExpression).value.slice(latsplit + 3, -4));
        }
        else if(ttag === ExpressionTag.LiteralComplexNumberExpression) {
            const cnv = (exp as LiteralSimpleExpression).value;
            let spos = cnv.lastIndexOf("+");
            if(spos === -1) {
                spos = cnv.lastIndexOf("-");
            }

            return new IRLiteralComplexExpression(cnv.slice(0, spos), cnv.slice(spos, -1));
        }
        else if(ttag === ExpressionTag.LiteralByteBufferExpression) {
            const bytes = (exp as LiteralSimpleExpression).value.slice(3, -1).split(",").map((b) => parseInt("0x" + b, 16));
            return new IRLiteralByteBufferExpression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralUUIDv4Expression) {
            const bstring = (exp as LiteralSimpleExpression).value.slice(6, -1).replace(/-/g, "");
            let bytes: number[] = [];
            for(let i = 0; i < bstring.length; i += 2) {
                bytes.push(parseInt("0x" + bstring.slice(i, i + 2), 16));
            }

            return new IRLiteralUUIDv4Expression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralUUIDv7Expression) {
            const bstring = (exp as LiteralSimpleExpression).value.slice(6, -1).replace(/-/g, "");
            let bytes: number[] = [];
            for(let i = 0; i < bstring.length; i += 2) {
                bytes.push(parseInt("0x" + bstring.slice(i, i + 2), 16));
            }

            return new IRLiteralUUIDv7Expression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralSHAContentHashExpression) {
            const bstring = (exp as LiteralSimpleExpression).value.slice(5, -1)
            let bytes: number[] = [];
            for(let i = 0; i < bstring.length; i += 2) {
                bytes.push(parseInt("0x" + bstring.slice(i, i + 2), 16));
            }

            return new IRLiteralSHAContentHashExpression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralTZDateTimeExpression) {
            const dstri = (exp as LiteralSimpleExpression).value.split("T@");
            const datepart = ASMToIRConverter.extractLiteralDateInfo(dstri[0]);
            const timepart = ASMToIRConverter.extractLiteralTimeInfo(dstri[1]);

            return new IRLiteralTZDateTimeExpression(datepart, timepart, dstri[2]);
        }
        else if(ttag === ExpressionTag.LiteralTAITimeExpression) {
            const dstri = (exp as LiteralSimpleExpression).value.split("T");
            const datepart = ASMToIRConverter.extractLiteralDateInfo(dstri[0]);
            const timepart = ASMToIRConverter.extractLiteralTimeInfo(dstri[1]);

            return new IRLiteralTAITimeExpression(datepart, timepart);
        }
        else if(ttag === ExpressionTag.LiteralPlainDateExpression) {
            return new IRLiteralPlainDateExpression(ASMToIRConverter.extractLiteralDateInfo((exp as LiteralSimpleExpression).value));
        }
        else if(ttag === ExpressionTag.LiteralPlainTimeExpression) {
            return new IRLiteralPlainTimeExpression(ASMToIRConverter.extractLiteralTimeInfo((exp as LiteralSimpleExpression).value));
        }
        else if(ttag === ExpressionTag.LiteralLogicalTimeExpression) {
            return new IRLiteralLogicalTimeExpression((exp as LiteralSimpleExpression).value.slice(-2));
        }
        else if(ttag === ExpressionTag.LiteralISOTimeStampExpression) {
            const dstri = (exp as LiteralSimpleExpression).value.slice(0, -1).split("T.");
            const datepart = ASMToIRConverter.extractLiteralDateInfo(dstri[0]);
            const timepart = ASMToIRConverter.extractLiteralTimeInfo(dstri[1]);

            return new IRLiteralISOTimeStampExpression(datepart, timepart, Number.parseInt(dstri[2].slice(0, -1), 10));
        }
        else if(ttag === ExpressionTag.LiteralDeltaDateTimeExpression) {
            const sign = (exp as LiteralSimpleExpression).value[0] as "+" | "-";
            const dstri = (exp as LiteralSimpleExpression).value.slice(1).split("T");
            const deltadatepart = ASMToIRConverter.extractLiteralDeltaDateInfo(dstri[0]);
            const deltatimepart = ASMToIRConverter.extractLiteralDeltaTimeInfo(dstri[1]);
            
            return new IRLiteralDeltaDateTimeExpression(sign, deltadatepart, deltatimepart);
        }
        else if(ttag === ExpressionTag.LiteralDeltaISOTimeStampExpression) {
            const sign = (exp as LiteralSimpleExpression).value[0] as "+" | "-";
            const dstri = (exp as LiteralSimpleExpression).value.slice(1, -1).split("T.");
            const deltadatepart = ASMToIRConverter.extractLiteralDeltaDateInfo(dstri[0]);
            const deltatimepart = ASMToIRConverter.extractLiteralDeltaTimeInfo(dstri[1]);
            const deltamilliseconds = BigInt(dstri[2]);

            return new IRLiteralDeltaISOTimeStampExpression(sign, deltadatepart, deltatimepart, deltamilliseconds);
        }
        else if(ttag === ExpressionTag.LiteralDeltaSecondsExpression) {
            const sign = (exp as LiteralSimpleExpression).value[0] as "+" | "-";
            const seconds = (exp as LiteralSimpleExpression).value.slice(1, -2);

            return new IRLiteralDeltaSecondsExpression(sign, seconds);
        }
        else if(ttag === ExpressionTag.LiteralDeltaLogicalExpression) {
            const sign = (exp as LiteralSimpleExpression).value[0] as "+" | "-";
            const ticks = (exp as LiteralSimpleExpression).value.slice(1, -2);

            return new IRLiteralDeltaLogicalTimeExpression(sign, ticks);
        }
        else if(ttag === ExpressionTag.LiteralUnicodeRegexExpression) {
            const rexp = (exp as LiteralRegexExpression);
            const regexinst = this.processRegex(rexp.inns, rexp.value);

            return new IRLiteralUnicodeRegexExpression(regexinst.regexID, rexp.value);
        }
        else if(ttag === ExpressionTag.LiteralCRegexExpression) {
            const rexp = (exp as LiteralRegexExpression);
            const regexinst = this.processRegex(rexp.inns, rexp.value);

            return new IRLiteralCRegexExpression(regexinst.regexID, rexp.value);
        }
        else if(ttag === ExpressionTag.LiteralByteExpression) {
            const bstr = (exp as LiteralSimpleExpression).value;
            const nval = Number.parseInt(bstr, 16);
            return new IRLiteralByteExpression(nval);
        }
        else if(ttag === ExpressionTag.LiteralCCharExpression) {
            return new IRLiteralCCharExpression(((exp as LiteralSimpleExpression).resolvedValue as string).charCodeAt(0));
        }
        else if(ttag === ExpressionTag.LiteralUnicodeCharExpression) {
            return new IRLiteralUnicodeCharExpression(((exp as LiteralSimpleExpression).resolvedValue as string).charCodeAt(0));
        }
        else if(ttag === ExpressionTag.LiteralCStringExpression) {
            const slexp = exp as LiteralCStringExpression;
            const bytes = this.processStringBytes(slexp.resolvedValue as string);

            return new IRLiteralCStringExpression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralStringExpression) {
            const slexp = exp as LiteralStringExpression;
            const bytes = this.processStringBytes(slexp.resolvedValue as string);

            return new IRLiteralStringExpression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralFormatStringExpression) {
            const ffmt = exp as LiteralFormatStringExpression;
            const fmts = ffmt.fmts.map<IRFormatStringComponent>((fmtcomp) => {
                if(fmtcomp instanceof FormatStringTextComponent) {
                    const slexp = fmtcomp as FormatStringTextComponent;
                    const bytes = this.processStringBytes(slexp.resolvedValue as string);

                    return new IRFormatStringTextComponent(bytes);
                }
                else {
                    const argexp = fmtcomp as FormatStringArgComponent;
                    return new IRFormatStringArgComponent(argexp.argPos, this.processTypeSignature(argexp.resolvedType as TypeSignature));
                }
            });

            return new IRLiteralFormatStringExpression(fmts);
        }
        else if(ttag === ExpressionTag.LiteralFormatCStringExpression) {
            const ffmt = exp as LiteralFormatCStringExpression;
            const fmts = ffmt.fmts.map<IRFormatStringComponent>((fmtcomp) => {
                if(fmtcomp instanceof FormatStringTextComponent) {
                    const slexp = fmtcomp as FormatStringTextComponent;
                    const bytes = this.processStringBytes(slexp.resolvedValue as string);

                    return new IRFormatStringTextComponent(bytes);
                }
                else {
                    const argexp = fmtcomp as FormatStringArgComponent;
                    return new IRFormatStringArgComponent(argexp.argPos, this.processTypeSignature(argexp.resolvedType as TypeSignature));
                }
            });

            return new IRLiteralFormatCStringExpression(fmts);
        }
        else if(ttag === ExpressionTag.LiteralTypeDeclValueExpression) {
            const tdeclexp = exp as LiteralTypeDeclValueExpression;
            
            const csig = this.processTypeSignature(tdeclexp.constype);
            const iexp = this.flattenExpression(tdeclexp.value);
            if((tdeclexp.constype as NominalTypeSignature).decl.allInvariants.length > 0) {
                const invchecks = (tdeclexp.constype as NominalTypeSignature).decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                    return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, iexp);
                });

                this.pushStatements(invchecks);
            }

            return new IRLiteralTypedExpression(iexp as IRLiteralExpression, csig);
        }
        else if(ttag === ExpressionTag.LiteralTypedStringExpression) {
            let tdeclexp = exp as LiteralTypedStringExpression;
            
            const bytes = this.processStringBytes(tdeclexp.resolvedValue as string);
            const csig = this.processTypeSignature(tdeclexp.constype);
            const iexp = new IRLiteralStringExpression(bytes);

            if((tdeclexp.constype as NominalTypeSignature).decl.allInvariants.length > 0) {
                const invchecks = (tdeclexp.constype as NominalTypeSignature).decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                    return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, iexp);
                });

                this.pushStatements(invchecks);
            }

            return new IRLiteralTypedStringExpression(bytes, csig);
        }
        else if(ttag === ExpressionTag.LiteralTypedCStringExpression) {
            let tdeclexp = exp as LiteralTypedCStringExpression;
            
            const bytes = this.processStringBytes(tdeclexp.resolvedValue as string);
            const csig = this.processTypeSignature(tdeclexp.constype);
            const iexp = new IRLiteralCStringExpression(bytes);

            if((tdeclexp.constype as NominalTypeSignature).decl.allInvariants.length > 0) {
                const invchecks = (tdeclexp.constype as NominalTypeSignature).decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                    return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, iexp);
                });
                
                this.pushStatements(invchecks);
            }

            return new IRLiteralTypedCStringExpression(bytes, csig);
        }
        else if(ttag === ExpressionTag.LiteralTypedFormatStringExpression) {
            const ffmt = exp as LiteralTypedFormatStringExpression;
            const fmts = ffmt.fmts.map<IRFormatStringComponent>((fmtcomp) => {
                if(fmtcomp instanceof FormatStringTextComponent) {
                    const slexp = fmtcomp as FormatStringTextComponent;
                    const bytes = this.processStringBytes(slexp.resolvedValue as string);

                    return new IRFormatStringTextComponent(bytes);
                }
                else {
                    const argexp = fmtcomp as FormatStringArgComponent;
                    return new IRFormatStringArgComponent(argexp.argPos, this.processTypeSignature(argexp.resolvedType as TypeSignature));
                }
            });

            const csig = this.processTypeSignature(ffmt.constype);
            return new IRLiteralTypedFormatStringExpression(csig, fmts);
        }
        else if(ttag === ExpressionTag.LiteralTypedFormatCStringExpression) {
            const ffmt = exp as LiteralTypedFormatCStringExpression;
            const fmts = ffmt.fmts.map<IRFormatStringComponent>((fmtcomp) => {
                if(fmtcomp instanceof FormatStringTextComponent) {
                    const slexp = fmtcomp as FormatStringTextComponent;
                    const bytes = this.processStringBytes(slexp.resolvedValue as string);

                    return new IRFormatStringTextComponent(bytes);
                }
                else {
                    const argexp = fmtcomp as FormatStringArgComponent;
                    return new IRFormatStringArgComponent(argexp.argPos, this.processTypeSignature(argexp.resolvedType as TypeSignature));
                }
            });

            const csig = this.processTypeSignature(ffmt.constype);
            return new IRLiteralTypedFormatCStringExpression(csig, fmts);
        } 
        else if(ttag === ExpressionTag.AccessEnvValueExpression) {
            const aevexp = exp as AccessEnvValueExpression;

            const kbytes = this.processStringBytes(aevexp.resolvedkey as string);
            if(aevexp.opname === "has") {
                return new IRAccessEnvHasExpression(kbytes);
            }
            else if(aevexp.opname === "get"){
                if(!aevexp.mustdefined) {
                    this.pushStatement(new IRPreconditionCheckStatement(this.currentFile as string, exp.sinfo, undefined, this.errCtr++, "env::get", 0, [new IRAccessEnvHasExpression(kbytes)]));
                }

                return new IRAccessEnvGetExpression(kbytes, this.processTypeSignature(aevexp.optoftype as TypeSignature));
            }
            else {
                return new IRAccessEnvTryGetExpression(kbytes, this.processTypeSignature(aevexp.optoftype as TypeSignature), this.processTypeSignature(exp.getType()));
            }
        }
        else if(ttag === ExpressionTag.TaskAccessIDExpression) {
            const taexp = exp as TaskAccessInfoExpression;
            if(taexp.name === "currentID") {
                return new IRTaskAccessIDExpression();
            }
            else {
                return new IRTaskAccessParentIDExpression();
            }
        }
        else if(ttag === ExpressionTag.AccessNamespaceConstantExpression) {
            const tnsa = exp as AccessNamespaceConstantExpression;
            const rvv = this.assembly.tryReduceConstantExpression(tnsa);
            if(rvv !== undefined) {
                return this.flattenExpression(rvv);
            }
            else {
                const flatconstname = `${tnsa.ns.emit()}::${tnsa.name}()`;
                return new IRAccessNamespaceConstantExpression(flatconstname);
            }
        }
        else if(ttag === ExpressionTag.AccessStaticFieldExpression) {
            const tasf = exp as AccessStaticFieldExpression;
            const rvv = this.assembly.tryReduceConstantExpression(tasf);
            if(rvv !== undefined) {
                return this.flattenExpression(rvv);
            }
            else {
                const flatfieldname = `${(tasf.resolvedDeclType as TypeSignature).emit()}::${tasf.name}()`;
                return new IRAccessStaticFieldExpression(flatfieldname);
            }
        }
        else if(ttag === ExpressionTag.AccessEnumExpression) {
            const taee = exp as AccessEnumExpression;
            const flatenumname = `${taee.stype.emit()}::${taee.name}`;

            return new IRAccessEnumExpression(flatenumname);
        }
        else if(ttag === ExpressionTag.AccessVariableExpression) {
            const tave = exp as AccessVariableExpression;

            if(tave.isParameter) {
                return new IRAccessParameterVariableExpression(tave.srcname);
            }
            else if(tave.isCaptured) {
                return new IRAccessCapturedVariableExpression(tave.scopeidx as number, this.processLocalVariableName(tave.srcname));
            }
            else {
                return new IRAccessLocalVariableExpression(this.processLocalVariableName(tave.srcname));
            }
        }
        else if(ttag === ExpressionTag.ConstructorPrimaryExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.ConstructorEListExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.ConstructorLambdaExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.LambdaInvokeExpression) {
            return this.flattenLambdaInvokeExpression(exp as LambdaInvokeExpression);
        }
        else if(ttag === ExpressionTag.SpecialConstructorExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.CallNamespaceFunctionExpression) {
            return this.flattenCallNamespaceFunctionExpression(exp as CallNamespaceFunctionExpression);
        }
        else if(ttag === ExpressionTag.CallTypeFunctionExpression) {
            return this.flattenCallTypeFunctionExpression(exp as CallTypeFunctionExpression);
        }
        else if(ttag === ExpressionTag.ParseAsTypeExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.PostfixOpExpression) {
            return this.flattenPostfixOp(exp as PostfixOp);
        }
        else if(ttag === ExpressionTag.PrefixNotOpExpression) {
            const pfxnot = exp as PrefixNotOpExpression;
            const eetype = pfxnot.exp.getType() as NominalTypeSignature;
            const nexp = this.makeExpressionSimple(this.flattenExpression(pfxnot.exp), eetype);
            
            if(!(eetype.decl instanceof TypedeclTypeDecl)) {
                return new IRPrefixNotOpExpression(nexp, this.processTypeSignature(pfxnot.opertype as TypeSignature));
            }
            else {
                const tdaccess = new IRAccessTypeDeclValueExpression(this.processTypeSignature(eetype), nexp);
                const notop = new IRPrefixNotOpExpression(tdaccess, this.processTypeSignature(pfxnot.opertype as TypeSignature));

                if(eetype.decl.allInvariants.length !== 0) {
                    const invchecks = eetype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, notop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(eetype), notop);
            }
        }
        else if(ttag === ExpressionTag.PrefixNegateOrPlusOpExpression) {
            const pfxneg = exp as PrefixNegateOrPlusOpExpression;
            const eetype = pfxneg.exp.getType() as NominalTypeSignature;
            const nexp = this.makeExpressionSimple(this.flattenExpression(pfxneg.exp), eetype);
            
            if(!(eetype.decl instanceof TypedeclTypeDecl)) {
                return pfxneg.op === "-" ? new IRPrefixNegateOpExpression(nexp, this.processTypeSignature(pfxneg.opertype as TypeSignature)) : nexp;
            }
            else {
                const tdaccess = new IRAccessTypeDeclValueExpression(this.processTypeSignature(eetype), nexp);
                const nsop = pfxneg.op === "-" ? new IRPrefixNegateOpExpression(tdaccess, this.processTypeSignature(pfxneg.opertype as TypeSignature)) : tdaccess;

                if(eetype.decl.allInvariants.length !== 0) {
                    const invchecks = eetype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, nsop);
                    });
                
                    this.pushStatements(invchecks);
                }
                
                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(eetype), nsop);
            }
        }
        else if(ttag === ExpressionTag.BinAddExpression) {
            const binadd = exp as BinAddExpression;
            const finaltype = binadd.getType() as NominalTypeSignature;
            const leetype = binadd.lhs.getType() as NominalTypeSignature;
            const reetype = binadd.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(binadd.lhs), this.flattenExpression(binadd.rhs), leetype, reetype);

            const opchk = (binadd.opertype as TypeSignature).tkeystr as "Nat" | "Int" | "ChkNat" | "ChkInt";
            this.pushStatement(new IRErrorAdditionBoundsCheckStatement(this.currentFile as string, binadd.sinfo, this.errCtr++, lexp, rexp, opchk));

            if(!(finaltype.decl instanceof TypedeclTypeDecl)) {
                return new IRBinAddExpression(lexp, rexp, this.processTypeSignature(binadd.opertype as TypeSignature));
            }
            else {
                const addop = new IRBinAddExpression(lexp, rexp, this.processTypeSignature(binadd.opertype as TypeSignature));

                if(finaltype.decl.allInvariants.length !== 0) {
                    const invchecks = finaltype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, addop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(finaltype), addop);
            }
        }
        else if(ttag === ExpressionTag.BinSubExpression) {
            const binsub = exp as BinSubExpression;
            const finaltype = binsub.getType() as NominalTypeSignature;
            const leetype = binsub.lhs.getType() as NominalTypeSignature;
            const reetype = binsub.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(binsub.lhs), this.flattenExpression(binsub.rhs), leetype, reetype);

            const opchk = (binsub.opertype as TypeSignature).tkeystr as "Nat" | "Int" | "ChkNat" | "ChkInt";
            this.pushStatement(new IRErrorSubtractionBoundsCheckStatement(this.currentFile as string, binsub.sinfo, this.errCtr++, lexp, rexp, opchk));

            if(!(finaltype.decl instanceof TypedeclTypeDecl)) {
                return new IRBinSubExpression(lexp, rexp, this.processTypeSignature(binsub.opertype as TypeSignature));
            }
            else {
                const subop = new IRBinSubExpression(lexp, rexp, this.processTypeSignature(binsub.opertype as TypeSignature));

                if(finaltype.decl.allInvariants.length !== 0) {
                    const invchecks = finaltype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, subop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(finaltype), subop);
            }
        }
        else if(ttag === ExpressionTag.BinMultExpression) {
            const binmult = exp as BinMultExpression;
            const finaltype = binmult.getType() as NominalTypeSignature;
            const leetype = binmult.lhs.getType() as NominalTypeSignature;
            const reetype = binmult.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(binmult.lhs), this.flattenExpression(binmult.rhs), leetype, reetype);

            const opchk = (binmult.opertype as TypeSignature).tkeystr as "Nat" | "Int" | "ChkNat" | "ChkInt";
            this.pushStatement(new IRErrorMultiplicationBoundsCheckStatement(this.currentFile as string, binmult.sinfo, this.errCtr++, lexp, rexp, opchk));

            if(!(finaltype.decl instanceof TypedeclTypeDecl)) {
                return new IRBinMultExpression(lexp, rexp, this.processTypeSignature(binmult.opertype as TypeSignature));
            }
            else {
                const multop = new IRBinMultExpression(lexp, rexp, this.processTypeSignature(binmult.opertype as TypeSignature));

                if(finaltype.decl.allInvariants.length !== 0) {
                    const invchecks = finaltype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, multop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(finaltype), multop);
            }
        }
        else if(ttag === ExpressionTag.BinDivExpression) {
            const bindiv = exp as BinDivExpression;
            const finaltype = bindiv.getType() as NominalTypeSignature;
            const leetype = bindiv.lhs.getType() as NominalTypeSignature;
            const reetype = bindiv.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(bindiv.lhs), this.flattenExpression(bindiv.rhs), leetype, reetype);

            const opchk = (bindiv.opertype as TypeSignature).tkeystr as "Nat" | "Int" | "ChkNat" | "ChkInt";
            this.pushStatement(new IRErrorDivisionByZeroCheckStatement(this.currentFile as string, bindiv.sinfo, this.errCtr++, lexp, rexp, opchk));

            if(!(finaltype.decl instanceof TypedeclTypeDecl)) {
                return new IRBinDivExpression(lexp, rexp, this.processTypeSignature(bindiv.opertype as TypeSignature));
            }
            else {
                const divop = new IRBinDivExpression(lexp, rexp, this.processTypeSignature(bindiv.opertype as TypeSignature));

                if(finaltype.decl.allInvariants.length !== 0) {
                    const invchecks = finaltype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, divop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(finaltype), divop);
            }
        }
        else if(ttag === ExpressionTag.BinKeyEqExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.BinKeyNeqExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.KeyCompareEqExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.KeyCompareLessExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.NumericEqExpression) {
            const neqexp = exp as NumericEqExpression;
            const leetype = neqexp.lhs.getType() as NominalTypeSignature;
            const reetype = neqexp.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(neqexp.lhs), this.flattenExpression(neqexp.rhs), leetype, reetype);

            return new IRNumericEqExpression(lexp, rexp, this.processTypeSignature(neqexp.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericNeqExpression) {
            const nneqexp = exp as NumericNeqExpression;
            const leetype = nneqexp.lhs.getType() as NominalTypeSignature;
            const reetype = nneqexp.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(nneqexp.lhs), this.flattenExpression(nneqexp.rhs), leetype, reetype);

            return new IRNumericNeqExpression(lexp, rexp, this.processTypeSignature(nneqexp.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericLessExpression) {
            const nless = exp as NumericLessExpression;
            const leetype = nless.lhs.getType() as NominalTypeSignature;
            const reetype = nless.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(nless.lhs), this.flattenExpression(nless.rhs), leetype, reetype);

            return new IRNumericLessExpression(lexp, rexp, this.processTypeSignature(nless.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericLessEqExpression) {
            const nlesseq = exp as NumericLessEqExpression;
            const leetype = nlesseq.lhs.getType() as NominalTypeSignature;
            const reetype = nlesseq.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(nlesseq.lhs), this.flattenExpression(nlesseq.rhs), leetype, reetype);

            return new IRNumericLessEqExpression(lexp, rexp, this.processTypeSignature(nlesseq.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericGreaterExpression) {
            const ngreater = exp as NumericGreaterExpression;
            const leetype = ngreater.lhs.getType() as NominalTypeSignature;
            const reetype = ngreater.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(ngreater.lhs), this.flattenExpression(ngreater.rhs), leetype, reetype);

            return new IRNumericGreaterExpression(lexp, rexp, this.processTypeSignature(ngreater.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericGreaterEqExpression) {
            const ngreatereq = exp as NumericGreaterEqExpression;
            const leetype = ngreatereq.lhs.getType() as NominalTypeSignature;
            const reetype = ngreatereq.rhs.getType() as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(ngreatereq.lhs), this.flattenExpression(ngreatereq.rhs), leetype, reetype);

            return new IRNumericGreaterEqExpression(lexp, rexp, this.processTypeSignature(ngreatereq.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.LogicAndExpression) {
            const landexp = exp as LogicAndExpression;
            const landargs = landexp.exps.map<[IRExpression, IRTypeSignature]>((argexp) => [this.makeExpressionSimple(this.flattenExpression(argexp), argexp.getType() as NominalTypeSignature), this.processTypeSignature(argexp.getType())]);

            if(landargs.some((a) => ASMToIRConverter.isLiteralFalseExpression(a[0]))) {
                //if one arg was a literal bool then the return must also be a bool type (namely false)
                return new IRLiteralBoolExpression(false);
            }
            else {
                let resbool: IRSimpleExpression;
                const filteredargs = landargs.filter((a) => !ASMToIRConverter.isLiteralTrueExpression(a[0]));
                if(filteredargs.length === 1) {
                    if(filteredargs[0][1].tkeystr === "Bool") {
                        resbool = filteredargs[0][0];
                    }
                    else {
                        resbool = new IRAccessTypeDeclValueExpression(filteredargs[0][1], filteredargs[0][0]);
                    }
                }
                else {
                    const allexps = filteredargs.map((a) => (a[1].tkeystr !== "Bool") ? new IRAccessTypeDeclValueExpression(a[1], a[0]) : a[0]);
                    resbool = new IRLogicAndExpression(allexps);
                }

                if(exp.getType().tkeystr === "Bool") {
                    return resbool;
                }
                else {
                    if((exp.getType() as NominalTypeSignature).decl.allInvariants.length !== 0) {
                        const invchecks = (exp.getType() as NominalTypeSignature).decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                            return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, resbool);
                        });
                
                        this.pushStatements(invchecks);
                    }

                    return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(exp.getType()), resbool);
                }
            }
        }
        else if(ttag === ExpressionTag.LogicOrExpression) {
            const lorexp = exp as LogicOrExpression;
            const lorargs = lorexp.exps.map<[IRExpression, IRTypeSignature]>((argexp) => [this.makeExpressionSimple(this.flattenExpression(argexp), argexp.getType() as NominalTypeSignature), this.processTypeSignature(argexp.getType())]);

            if(lorargs.some((a) => ASMToIRConverter.isLiteralTrueExpression(a[0]))) {
                //if one arg was a literal bool then the return must also be a bool type (namely true)
                return new IRLiteralBoolExpression(true);
            }
            else {
                let resbool: IRSimpleExpression;
                const filteredargs = lorargs.filter((a) => !ASMToIRConverter.isLiteralFalseExpression(a[0]));
                if(filteredargs.length === 1) {
                    if(filteredargs[0][1].tkeystr === "Bool") {
                        resbool = filteredargs[0][0];
                    }
                    else {
                        resbool = new IRAccessTypeDeclValueExpression(filteredargs[0][1], filteredargs[0][0]);
                    }
                }
                else {
                    const allexps = filteredargs.map((a) => (a[1].tkeystr !== "Bool") ? new IRAccessTypeDeclValueExpression(a[1], a[0]) : a[0]);
                    resbool = new IRLogicOrExpression(allexps);
                }

                if(exp.getType().tkeystr === "Bool") {
                    return resbool;
                }
                else {
                    if((exp.getType() as NominalTypeSignature).decl.allInvariants.length !== 0) {
                        const invchecks = (exp.getType() as NominalTypeSignature).decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                            return new IRTypeDeclInvariantCheckStatement(invdecl.file, invdecl.sinfo, invdecl.tag, this.errCtr++, invdecl.containingtype.tkeystr, invdecl.ii, resbool);
                        });
                
                        this.pushStatements(invchecks);
                    }

                    return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(exp.getType()), resbool);
                }
            }
        }
        else if(ttag === ExpressionTag.HoleExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else if(ttag === ExpressionTag.MapEntryConstructorExpression) {
            assert(false, `ASMToIRConverter: not implemented -- ${exp.tag}`);
        }
        else {
            assert(false, `ASMToIRConverter: Unsupported expression type -- ${exp.tag}`);
        }
    }

    private flattenCallRefVariableExpression(exp: CallRefVariableExpression): IRExpression {
        assert(false, "Not Implemented -- checkCallRefVariableExpression");
    }

    private flattenCallRefThisExpression(exp: CallRefThisExpression): IRExpression {
        assert(false, "Not Implemented -- checkCallRefThisExpression");
    }

    private flattenCallRefSelfExpression(exp: CallRefSelfExpression): IRExpression {
        assert(false, "Not Implemented -- checkCallRefSelfExpression");
    }

    private flattenCallTaskActionExpression(exp: CallTaskActionExpression): IRExpression {
        assert(false, "Not Implemented -- checkCallTaskActionExpression");
    }

    private flattenTaskRunExpression(exp: TaskRunExpression): IRExpression {
        assert(false, "Not Implemented -- instantiateTaskRunExpression");
    }

    private flattenTaskMultiExpression(exp: TaskMultiExpression): IRExpression {
        assert(false, "Not Implemented -- instantiateTaskMultiExpression");
    }

    private flattenTaskDashExpression(exp: TaskDashExpression): IRExpression {
        assert(false, "Not Implemented -- instantiateTaskDashExpression");
    }

    private flattenTaskAllExpression(exp: TaskAllExpression): IRExpression {
        assert(false, "Not Implemented -- instantiateTaskAllExpression");
    }

    private flattenTaskRaceExpression(exp: TaskRaceExpression): IRExpression {
        assert(false, "Not Implemented -- instantiateTaskRaceExpression");
    }

    private flattenAPIInvokeExpression(exp: APIInvokeExpression): IRExpression {
        assert(false, "Not Implemented");
    }
    
    private flattenAgentInvokeExpression(exp: AgentInvokeExpression): IRExpression {
        assert(false, "Not Implemented");
    }

    private flattenChkLogicExpression(exp: ChkLogicExpression): IRSimpleExpression {
        if(exp.tag === ChkLogicExpressionTag.ChkLogicBaseExpression) {
            const cle = exp as ChkLogicBaseExpression;

            return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenExpression(cle.exp), cle.exp.getType()), cle.exp.getType());
        }
        else {
            const iiexp = exp as ChkLogicImpliesExpression;
            const renv = this.flattenITestGuardSet(iiexp.sinfo, iiexp.lhs);

            if(iiexp.trueBinders.length === 0) {
                if(ASMToIRConverter.isLiteralFalseExpression(renv[0])) {
                    return new IRLiteralBoolExpression(true);
                }
                else {
                    this.pushStatementBlock();
                    const rhs = this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenExpression(iiexp.rhs), iiexp.rhs.getType()), iiexp.rhs.getType());
                    
                    const stmts = this.popStatementBlock();
                    if(stmts.length === 0) {
                        //no statements generated, so just return a simple expression directly
                        return new IRLogicOrExpression([new IRPrefixNotOpExpression(renv[0], this.processTypeSignature(this.getSpecialType(iiexp.sinfo, "Bool"))), rhs]);
                    }
                    else {
                        if(ASMToIRConverter.isLiteralTrueExpression(renv[0])) {
                            stmts.forEach((s) => this.pushStatement(s));
                            return rhs;
                        }
                        else {
                            const tvar = this.generateTempVarName();
                            this.pushStatement(new IRChkLogicImpliesShortCircuitStatement(tvar, renv[0], stmts, rhs));
                            return new IRAccessTempVariableExpression(tvar);
                        }
                    }
                }
            }
            else {
                assert(false, "Not implemented -- ChkLogicImpliesExpression with binders");
            }
        }
    }

    private flattenConditionalValueExpression(exp: ConditionalValueExpression): IRSimpleExpression {
        const renv = this.flattenITestGuardSet(exp.sinfo, exp.guardset);

        if(exp.trueBinders.length === 0 && exp.falseBinders.length === 0) {
            if(ASMToIRConverter.isLiteralTrueExpression(renv[0])) {
                return this.makeExpressionSimple(this.flattenExpression(exp.trueValue), exp.trueValue.getType());
            }
            else if(ASMToIRConverter.isLiteralFalseExpression(renv[0])) {
                return this.makeExpressionSimple(this.flattenExpression(exp.falseValue), exp.falseValue.getType());
            }
            else {
                this.pushStatementBlock();
                const texp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(this.flattenExpression(exp.trueValue), exp.trueValue.getType()), exp.trueValue.getType(), exp.rtype as TypeSignature);
                const fstmts = this.popStatementBlock();

                this.pushStatementBlock();
                const fexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(this.flattenExpression(exp.falseValue), exp.falseValue.getType()), exp.falseValue.getType(), exp.rtype as TypeSignature);
                const tstmts = this.popStatementBlock();

                if(tstmts.length === 0 && fstmts.length === 0) {
                    //no statements generated, so just return a simple expression directly
                    return new IRLogicSimpleConditionalExpression(renv[0], texp, fexp);
                }
                else {
                    const tvar = this.generateTempVarName();
                    const cbs = new IRLogicConditionalStatement(tvar, this.processTypeSignature(exp.rtype as TypeSignature), renv[0], tstmts, texp, fstmts, fexp);
                
                    this.pushStatement(cbs);
                    return new IRAccessTempVariableExpression(tvar);
                }
            }
        }
        else {
            assert(false, "Not implemented -- ConditionalValueExpression with binders");
        }
    }

    private flattenBaseRValueExpression(exp: Expression): IRExpression {
        const ttag = exp.tag;

        switch (ttag) {
            case ExpressionTag.CallRefVariableExpression: {
                return this.flattenCallRefVariableExpression(exp as CallRefVariableExpression);
            }
            case ExpressionTag.CallRefThisExpression: {
                return this.flattenCallRefThisExpression(exp as CallRefThisExpression);
            }
            case ExpressionTag.CallRefSelfExpression: {
                return this.flattenCallRefSelfExpression(exp as CallRefSelfExpression);
            }
            case ExpressionTag.CallTaskActionExpression: {
                return this.flattenCallTaskActionExpression(exp as CallTaskActionExpression);
            }
            case ExpressionTag.TaskRunExpression: {
                return this.flattenTaskRunExpression(exp as TaskRunExpression);
            }
            case ExpressionTag.TaskMultiExpression: {
                return this.flattenTaskMultiExpression(exp as TaskMultiExpression);
            }
            case ExpressionTag.TaskDashExpression: {
                return this.flattenTaskDashExpression(exp as TaskDashExpression);
            }
            case ExpressionTag.TaskAllExpression: {
                return this.flattenTaskAllExpression(exp as TaskAllExpression);
            }
            case ExpressionTag.TaskRaceExpression: {
                return this.flattenTaskRaceExpression(exp as TaskRaceExpression);
            }
            case ExpressionTag.APIInvokeExpression: {
                return this.flattenAPIInvokeExpression(exp as APIInvokeExpression);
            }
            case ExpressionTag.AgentInvokeExpression: {
                return this.flattenAgentInvokeExpression(exp as AgentInvokeExpression);
            }
            default: {
                return this.flattenExpression(exp);
            }
        }
    }

    private flattenExpressionRHS(exp: RValueExpression): IRExpression {
        const ttag = exp.tag;
        
        if(ttag === RValueExpressionTag.BaseExpression) {
            return this.flattenBaseRValueExpression((exp as BaseRValueExpression).exp);
        }
        else if(ttag === RValueExpressionTag.ShortCircuitAssignRHSExpressionFail) {
            assert(false, "Not Implemented -- checkShortCircuitAssignRHSFailExpression");
        }
        else if(ttag === RValueExpressionTag.ShortCircuitAssignRHSExpressionReturn) {
            assert(false, "Not Implemented -- checkShortCircuitAssignRHSReturnExpression");
        }
        else if(ttag === RValueExpressionTag.ConditionalValueExpression) {
            return this.flattenConditionalValueExpression(exp as ConditionalValueExpression);
        }
        else {
            assert(false, "Unknown RValueExpression kind");
        }
    }

    private flattenEmptyStatement(stmt: EmptyStatement) {
        this.pushStatement(new IRNopStatement());
    }

    private flattenVariableDeclarationStatement(stmt: VariableDeclarationStatement) {
        this.pushStatement(new IRVariableDeclarationStatement(this.processLocalVariableName(stmt.name), this.processTypeSignature(stmt.vtype)));
    }
    
    private flattenVariableMultiDeclarationStatement(stmt: VariableMultiDeclarationStatement) {
        for(let i = 0; i < stmt.decls.length; ++i) {
            const vdecl = stmt.decls[i];
            this.pushStatement(new IRVariableDeclarationStatement(this.processLocalVariableName(vdecl.name), this.processTypeSignature(vdecl.vtype)));
        }
    }

    private flattenVariableInitializationStatement(stmt: VariableInitializationStatement) {
        const irval = this.flattenExpressionRHS(stmt.exp);
        const irvtype = this.processTypeSignature(stmt.actualtype as TypeSignature);

        if(irval instanceof IRSimpleExpression) {
            const iconv = this.makeCoercionExplicitAsNeeded(irval, stmt.exp.rtype as TypeSignature, stmt.actualtype as TypeSignature, );
            this.pushStatement(new IRVariableInitializationStatement(this.processLocalVariableName(stmt.name), irvtype, iconv, stmt.vkind === "let"));
        }
        else if(irval instanceof IRInvokeDirectExpression) {
            if(irvtype.tkeystr === (stmt.exp.rtype as TypeSignature).tkeystr) {
                this.pushStatement(new IRVariableInitializationDirectInvokeStatement(this.generateTempVarName(), this.processLocalVariableName(stmt.name), irvtype, irval, stmt.vkind === "let"));    
            }
            else {
                const iiexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(irval, stmt.exp.rtype as TypeSignature), stmt.exp.rtype as TypeSignature, stmt.actualtype as TypeSignature);
                this.pushStatement(new IRVariableInitializationStatement(this.processLocalVariableName(stmt.name), irvtype, iiexp, stmt.vkind === "let"));
            }
        }
        else {
            assert(false, "ASMToIRConverter not implemented: VariableInitializationStatement value is not simple expression");
        }
    }

    private flattenVariableMultiInitializationStatement(stmt: VariableMultiInitializationStatement) {
       assert(false, "Not Implemented -- flattenVariableMultiInitializationStatement");
    }

    private flattenVariableAssignmentStatement(stmt: VariableAssignmentStatement) {
        assert(false, "Not Implemented -- flattenVariableAssignmentStatement");
    }

    private flattenVariableMultiAssignmentStatement(stmt: VariableMultiAssignmentStatement) {
        assert(false, "Not Implemented -- flattenVariableMultiAssignmentStatement");
    }

    private flattenReturnVoidStatement(stmt: ReturnVoidStatement) {
        if(this.currentImplicitReturnVar === undefined) {
            this.pushStatement(new IRReturnVoidSimpleStatement());
        }
        else {
            assert(false, "Not Implemented -- flattenReturnVoidStatement with implicit return variable");
        }
    }

    private flattenReturnSingleStatement(stmt: ReturnSingleStatement) {
        const irval = this.flattenExpressionRHS(stmt.value);

        if(this.currentImplicitReturnVar === undefined) {
            if(irval instanceof IRSimpleExpression) {
                this.pushStatement(new IRReturnValueSimpleStatement(irval));
            }
            else if(irval instanceof IRInvokeDirectExpression) {
                this.pushStatement(new IRReturnDirectInvokeStatement(irval));
            }
            else {
                assert(false, "ASMToIRConverter not implemented: need to do ref or simplify here");
            }
        }
    }

    private flattenReturnMultiStatement(stmt: ReturnMultiStatement) {
        assert(false, "Not Implemented -- flattenReturnMultiStatement");
    }

    private flattenIfStatement(stmt: IfStatement) {
        assert(false, "Not Implemented -- flattenIfStatement");
    }

    private flattenIfElseStatement(stmt: IfElseStatement) {
        assert(false, "Not Implemented -- flattenIfElseStatement");
    }

    private flattenIfElifElseStatement(stmt: IfElifElseStatement) {
        assert(false, "Not Implemented -- flattenIfElifElseStatement");
    }

    private flattenSwitchStatement(stmt: SwitchStatement) {
        assert(false, "Not Implemented -- flattenSwitchStatement");
    }

    private flattenMatchStatement(stmt: MatchStatement) {
        assert(false, "Not Implemented -- flattenMatchStatement");
    }

    private flattenDispatchPatternStatement(stmt: DispatchPatternStatement) {
        assert(false, "Not Implemented -- flattenDispatchPatternStatement");
    }

    private flattenDispatchTaskStatement(stmt: DispatchTaskStatement) {
        assert(false, "Not Implemented -- flattenDispatchTaskStatement");
    }

    private flattenAbortStatement(stmt: AbortStatement) {
        this.pushStatement(new IRAbortStatement(this.currentFile as string, stmt.sinfo, undefined, this.errCtr++));
    }

    private flattenAssertStatement(stmt: AssertStatement) {
        const ircond = this.flattenChkLogicExpression(stmt.cond);
        if(ASMToIRConverter.isLiteralTrueExpression(ircond)) {
            ;//no-op
        }
        else {
            this.pushStatement(new IRAssertStatement(this.currentFile as string, stmt.sinfo, stmt.tag, this.errCtr++, ircond));
        }
    }
    
    private flattenValidateStatement(stmt: ValidateStatement) {
        const ircond = this.flattenChkLogicExpression(stmt.cond);
        if(ASMToIRConverter.isLiteralTrueExpression(ircond)) {
            ;//no-op
        }
        else {
            this.pushStatement(new IRValidateStatement(this.currentFile as string, stmt.sinfo, stmt.tag, this.errCtr++, ircond));
        }
    }

    private flattenDebugStatement(stmt: DebugStatement) {
        const irval = this.makeExpressionSimple(this.flattenExpression(stmt.value), stmt.value.getType());
        const irtype = this.processTypeSignature(stmt.value.getType());

        this.pushStatement(new IRDebugStatement(irtype, irval, this.currentFile as string, stmt.sinfo));
    }

    private flattenVoidRefCallStatement(stmt: VoidRefCallStatement) {
        assert(false, "Not Implemented -- flattenVoidRefCallStatement");
    }

    private flattenVarUpdateStatement(stmt: VarUpdateStatement) {
        assert(false, "Not Implemented -- flattenVarUpdateStatement");
    }

    private flattenThisUpdateStatement(stmt: ThisUpdateStatement) {
        assert(false, "Not Implemented -- flattenThisUpdateStatement");
    }

    private flattenSelfUpdateStatement(stmt: SelfUpdateStatement) {
        assert(false, "Not Implemented -- flattenSelfUpdateStatement");
    }

    private flattenHoleStatement(stmt: HoleStatement) {
        assert(false, "Not Implemented -- flattenHoleStatement");
    }

    private flattenTaskStatusStatement(stmt: TaskStatusStatement) {
        assert(false, "Not Implemented -- flattenTaskStatusStatement");
    }

    private flattenTaskCheckAndHandleTerminationStatement(stmt: TaskCheckAndHandleTerminationStatement) {
        assert(false, "Not Implemented -- flattenTaskCheckAndHandleTerminationStatement");
    }

    private flattenTaskYieldStatement(stmt: TaskYieldStatement) {
        assert(false, "Not Implemented -- flattenTaskYieldStatement");
    }

    private flattenBlockStatement(stmt: BlockStatement) {
        for(let i = 0; i < stmt.statements.length; ++i) {
            this.flattenStatement(stmt.statements[i]);
        }
    }

    private flattenStatement(stmt: Statement) {
        switch(stmt.tag) {
            case StatementTag.EmptyStatement: {
                this.flattenEmptyStatement(stmt as EmptyStatement);
                break;
            }
            case StatementTag.VariableDeclarationStatement: {
                this.flattenVariableDeclarationStatement(stmt as VariableDeclarationStatement);
                break;
            }
            case StatementTag.VariableMultiDeclarationStatement: {
                this.flattenVariableMultiDeclarationStatement(stmt as VariableMultiDeclarationStatement);
                break;
            }
            case StatementTag.VariableInitializationStatement: {
                this.flattenVariableInitializationStatement(stmt as VariableInitializationStatement);
                break;
            }
            case StatementTag.VariableMultiInitializationStatement: {
                this.flattenVariableMultiInitializationStatement(stmt as VariableMultiInitializationStatement);
                break;
            }
            case StatementTag.VariableAssignmentStatement: {
                this.flattenVariableAssignmentStatement(stmt as VariableAssignmentStatement);
                break;
            }
            case StatementTag.VariableMultiAssignmentStatement: {
                this.flattenVariableMultiAssignmentStatement(stmt as VariableMultiAssignmentStatement);
                break;
            }
            case StatementTag.ReturnVoidStatement: {
                this.flattenReturnVoidStatement(stmt as ReturnVoidStatement);
                break;
            }
            case StatementTag.ReturnSingleStatement: {
                this.flattenReturnSingleStatement(stmt as ReturnSingleStatement);
                break;
            }
            case StatementTag.ReturnMultiStatement: {
                this.flattenReturnMultiStatement(stmt as ReturnMultiStatement);
                break;
            }
            case StatementTag.IfStatement: {
                this.flattenIfStatement(stmt as IfStatement);
                break;
            }
            case StatementTag.IfElseStatement: {
                this.flattenIfElseStatement(stmt as IfElseStatement);
                break;
            }
            case StatementTag.IfElifElseStatement: {
                this.flattenIfElifElseStatement(stmt as IfElifElseStatement);
                break;
            }
            case StatementTag.SwitchStatement: {
                this.flattenSwitchStatement(stmt as SwitchStatement);
                break;
            }
            case StatementTag.MatchStatement: {
                this.flattenMatchStatement(stmt as MatchStatement);
                break;
            }
            case StatementTag.DispatchPatternStatement: {
                this.flattenDispatchPatternStatement(stmt as DispatchPatternStatement);
                break;
            }
            case StatementTag.DispatchTaskStatement: {
                this.flattenDispatchTaskStatement(stmt as DispatchTaskStatement);
                break;
            }
            case StatementTag.AbortStatement: {
                this.flattenAbortStatement(stmt as AbortStatement);
                break;
            }
            case StatementTag.AssertStatement: {
                this.flattenAssertStatement(stmt as AssertStatement);
                break;
            }
            case StatementTag.ValidateStatement: {
                this.flattenValidateStatement(stmt as ValidateStatement);
                break;
            }
            case StatementTag.DebugStatement: {
                this.flattenDebugStatement(stmt as DebugStatement);
                break;
            }
            case StatementTag.VoidRefCallStatement: {
                this.flattenVoidRefCallStatement(stmt as VoidRefCallStatement);
                break;
            }
            case StatementTag.VarUpdateStatement: {
                this.flattenVarUpdateStatement(stmt as VarUpdateStatement);
                break;
            }
            case StatementTag.ThisUpdateStatement: {
                this.flattenThisUpdateStatement(stmt as ThisUpdateStatement);
                break;
            }
            case StatementTag.SelfUpdateStatement: {
                this.flattenSelfUpdateStatement(stmt as SelfUpdateStatement);
                break;
            }
            case StatementTag.HoleStatement: {
                this.flattenHoleStatement(stmt as HoleStatement);
                break;
            }
            case StatementTag.TaskStatusStatement: {
                this.flattenTaskStatusStatement(stmt as TaskStatusStatement);
                break;
            }
            case StatementTag.TaskCheckAndHandleTerminationStatement: {
                this.flattenTaskCheckAndHandleTerminationStatement(stmt as TaskCheckAndHandleTerminationStatement);
                break;
            }
            case StatementTag.TaskYieldStatement: {
                this.flattenTaskYieldStatement(stmt as TaskYieldStatement);
                break;
            }
            case StatementTag.BlockStatement: {
                this.flattenBlockStatement(stmt as BlockStatement);
                break;
            }
            default: {
                assert(false, `Unknown statement kind -- ${stmt.tag}`);
            }
        }
    }

    private flattenBodyImplementation(body: BodyImplementation) {
        if((body instanceof AbstractBodyImplementation) || (body instanceof PredicateUFBodyImplementation) || (body instanceof BuiltinBodyImplementation) || (body instanceof HoleBodyImplementation)) {
            return;
        }

        if(body instanceof ExpressionBodyImplementation) {
            this.flattenExpression(body.exp);
        }
        else {
            assert(body instanceof StandardBodyImplementation);
            
            for(let i = 0; i < body.statements.length; ++i) {
                this.flattenStatement(body.statements[i]);
            }
        }
    }

    private generateRequiresClauseExplicitInvoke(req: PreConditionDecl): IRInvokeDirectExpression {
        xxxx;
    }

    private generateEnsuresClauseExplicitInvoke(req: PreConditionDecl): IRInvokeDirectExpression {
        //TODO: ensures are in the generated body while requires are in caller?
        xxxx;
    }

    private generateInvariantClauseExplicitInvoke(req: PreConditionDecl): IRInvokeDirectExpression {
        xxxx;
    }

    private generateValidateClauseExplicitInvoke(req: PreConditionDecl): IRInvokeDirectExpression {
        xxxx;
    }

    private generateNamespaceFunctionDecl(asmdecl: NamespaceFunctionDecl): IRInvokeExpression {
        xxxx;
    }
}

export {
    ASMToIRConverter
};
