
import { SourceInfo } from "../../frontend/build_decls.js";
import { DashResultTypeSignature, EListTypeSignature, FormatPathTypeSignature, FormatStringTypeSignature, FullyQualifiedNamespace, LambdaTypeSignature, NominalTypeSignature, RecursiveAnnotation, TemplateNameMapper, TypeSignature, VoidTypeSignature } from "../../frontend/type.js";
import { AbortStatement, AccessEnumExpression, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, AgentInvokeExpression, APIInvokeExpression, AssertStatement, BaseRValueExpression, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallRefVariableExpression, CallTaskActionExpression, CallTypeFunctionExpression, ChkLogicBaseExpression, ChkLogicExpression, ChkLogicExpressionTag, ChkLogicImpliesExpression, ConditionalValueExpression, ConstructorPrimaryExpression, DebugStatement, DispatchPatternStatement, DispatchTaskStatement, EmptyStatement, Expression, ExpressionBodyImplementation, ExpressionTag, FormatStringArgComponent, FormatStringTextComponent, HoleBodyImplementation, HoleStatement, IfElifElseStatement, IfElseStatement, IfStatement, ITestGuard, ITestGuardSet, ITestSimpleGuard, KeyCompareEqExpression, KeyCompareLessExpression, LambdaInvokeExpression, LiteralCStringExpression, LiteralFormatCStringExpression, LiteralFormatStringExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralStringExpression, LiteralTypedCStringExpression, LiteralTypeDeclValueExpression, LiteralTypedFormatCStringExpression, LiteralTypedFormatStringExpression, LiteralTypedStringExpression, LogicAndExpression, LogicOrExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, PassingArgumentValue, PositionalArgumentValue, PostfixOp, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, RValueExpression, RValueExpressionTag, SelfUpdateStatement, SpecialConstructorExpression, StandardBodyImplementation, Statement, StatementTag, StdArgumentValue, SwitchStatement, TaskAccessInfoExpression, TaskAllExpression, TaskCheckAndHandleTerminationStatement, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VarUpdateStatement, VoidRefCallStatement } from "../../frontend/body.js";
import { AbstractCollectionTypeDecl, AbstractConceptTypeDecl, AbstractEntityTypeDecl, AdditionalTypeDeclTag, AgentDecl, APIDecl, APIDeniedTypeDecl, APIErrorTypeDecl, APIFlaggedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, ConstructableTypeDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, DeclarationAttibute, EntityTypeDecl, EnumTypeDecl, EventListTypeDecl, FailTypeDecl, InvariantDecl, InvokeParameterDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TaskDecl, TestAssociation, TypedeclTypeDecl, ValidateDecl } from "../../frontend/assembly.js";

import { IRDashResultTypeSignature, IREListTypeSignature, IRFormatCStringTypeSignature, IRFormatPathFragmentTypeSignature, IRFormatPathGlobTypeSignature, IRFormatPathTypeSignature, IRFormatStringTypeSignature, IRFormatTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature, IRVoidTypeSignature } from "../irdefs/irtype.js";
import { DateRepresentation, DeltaDateRepresentation, DeltaTimeRepresentation, IRLiteralChkIntExpression, IRLiteralChkNatExpression, IRLiteralBoolExpression, IRLiteralByteBufferExpression, IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralComplexExpression, IRLiteralCRegexExpression, IRLiteralCStringExpression, IRLiteralDecimalExpression, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaLogicalTimeExpression, IRLiteralDeltaSecondsExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralISOTimeStampExpression, IRLiteralLatLongCoordinateExpression, IRLiteralLogicalTimeExpression, IRLiteralNatExpression, IRLiteralNoneExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralRationalExpression, IRLiteralSHAContentHashExpression, IRLiteralStringExpression, IRLiteralTAITimeExpression, IRLiteralTZDateTimeExpression, IRLiteralUnicodeCharExpression, IRLiteralUnicodeRegexExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRStatement, TimeRepresentation, IRLiteralFormatStringExpression, IRFormatStringTextComponent, IRFormatStringArgComponent, IRFormatStringComponent, IRLiteralFormatCStringExpression, IRLiteralTypedExpression, IRLiteralExpression, IRTypeDeclInvariantCheckStatement, IRLiteralTypedStringExpression, IRLiteralTypedCStringExpression, IRLiteralTypedFormatStringExpression, IRLiteralTypedFormatCStringExpression, IRTaskAccessIDExpression, IRTaskAccessParentIDExpression, IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression, IRAccessConstantExpression, IRAccessEnumExpression, IRSimpleExpression, IRPreconditionCheckStatement, IRExpression, IRTempAssignExpressionStatement, IRAccessTempVariableExpression, IRAccessLocalVariableExpression, IRAccessCapturedVariableExpression, IRAccessParameterVariableExpression, IRPrefixNotOpExpression, IRAccessTypeDeclValueExpression, IRConstructSafeTypeDeclExpression, IRPrefixNegateOpExpression, IRBinAddExpression, IRErrorAdditionBoundsCheckStatement, IRBinSubExpression, IRBinMultExpression, IRBinDivExpression, IRErrorDivisionByZeroCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRNumericEqExpression, IRNumericNeqExpression, IRNumericLessExpression, IRNumericLessEqExpression, IRNumericGreaterExpression, IRNumericGreaterEqExpression, IRLogicAndExpression, IRLogicOrExpression, IRNopStatement, IRVariableDeclarationStatement, IRVariableInitializationStatement, IRReturnVoidSimpleStatement, IRAbortStatement, IRImmediateExpression, IRReturnValueSimpleStatement, IRChkLogicImpliesShortCircuitStatement, IRInvokeDirectExpression, IRLogicSimpleConditionalExpression, IRLogicConditionalStatement, IRVariableInitializationDirectInvokeStatement, IRInvokeSimpleExpression, IRInvokeImplicitsExpression, IRTempAssignStdInvokeStatement, IRTempAssignRefInvokeStatement, IRReturnDirectInvokeStatement, IRAssertStatement, IRValidateStatement, IRDebugStatement, IRBody, IRBuiltinBody, IRHoleBody, IRStandardBody, IRBinKeyEqDirectExpression, IRBinKeyLessDirectExpression, IRIsNoneOptionExpression, IRIsNotNoneOptionExpression, IRIsOptionEqValueExpression, IRIsOptionNeqValueExpression, IRIsSomeEqValueExpression, IRIsSomeNeqValueExpression, IRBinKeyNeqDirectExpression, IRConstructorOkTypeExpression, IRConstructorFailTypeExpression, IRConstructorSomeTypeExpression, IRConstructorMapEntryTypeExpression, IRLiteralDecimalDegreeExpression, IRTypeDeclSizeRangeCheckCStringStatement, IRTypeDeclSizeRangeCheckUnicodeStringStatement, IRTypeDeclFormatCheckCStringStatement, IRTypeDeclFormatCheckUnicodeStringStatement, IRLiteralOptionOfNoneExpression, IRWidenConceptRepresentationExpression, IRConstructResultFromOkExpression, IRConstructOptionFromSomeExpression, IRConstructResultFromFailExpression, IRBoxEntityToConceptRepresentationExpression, IRSimpleIfStatement, IRBlockStatement, IRSimpleIfElseStatement, IRConstructorStandardEntityExpression, IREntityInvariantCheckStatement, IRConstructExpression, IRVariableInitializationDirectConstructorStatement, IRReturnDirectConstructStatement, IRVariableAssignmentStatement, IRVariableAssignmentDirectInvokeStatement, IRVariableAssignmentDirectConstructorStatement, IRConstructorListEmptyExpression, IRConstructorListSingletonsExpression, IRReturnVoidWithImplicitStatement, IRReturnValueImplicitStatement, IRReturnDirectInvokeImplicitStatement, IRReturnDirectConstructWithBoxStatement, IRReturnDirectConstructImplicitStatement, IRReturnDirectConstructWithBoxImplicitStatement, IRReturnDirectInvokeImplicitPassThroughStatement, IRVariableInitializationDirectInvokeWithImplicitStatement, IRVariableAssignmentDirectInvokeWithImplicitStatement, IRInvokeSimpleWithImplicitsExpression, IRVoidInvokeStatement, IRVariableInitializationDirectConstructorWithBoxStatement, IRVariableAssignmentDirectConstructorWithBoxStatement } from "../irdefs/irbody.js";
import { IRRegex, IRSourceInfo } from "../irdefs/irsupport.js";
import { IRAgentDecl, IRAPIDecl, IRAPIDeniedTypeDecl, IRAPIErrorTypeDecl, IRAPIFlaggedTypeDecl, IRAPIRejectedTypeDecl, IRAPIResultTypeDecl, IRAPISuccessTypeDecl, IRAssembly, IRConceptTypeDecl, IRConstantDecl, IRDatatypeMemberEntityTypeDecl, IRDatatypeTypeDecl, IRDeclarationDocString, IRDeclarationMetaTag, IREntityTypeDecl, IREnumTypeDecl, IREventListTypeDecl, IRExampleDecl, IRFailTypeDecl, IRInvariantDecl, IRInvokeDecl, IRInvokeParameterDecl, IRListTypeDecl, IRMapEntryTypeDecl, IRMapTypeDecl, IRMemberFieldDecl, IROkTypeDecl, IROptionTypeDecl, IRPostConditionDecl, IRPreConditionDecl, IRPredicateDecl, IRPrimitiveEntityTypeDecl, IRQueueTypeDecl, IRResultTypeDecl, IRSetTypeDecl, IRSomeTypeDecl, IRStackTypeDecl, IRTaskDecl, IRTestAssociation, IRTestDecl, IRTypedeclCStringDecl, IRTypedeclStringDecl, IRTypedeclTypeDecl, IRValidateDecl } from "../irdefs/irassembly.js";

import { InvokeInstantiationInfo, NamespaceInstantiationInfo, TypeInstantiationInfo } from "./instantiations.js";

import assert from "node:assert";

class ASMToIRConverter {
    readonly assembly: Assembly;

    readonly generateTestInfo: boolean;
    readonly testfilefilter: string[] | undefined;
    readonly testfilters: TestAssociation[] | undefined;

    regexs: IRRegex[];
    elists: IREListTypeSignature[];
    dashtypes: IRDashResultTypeSignature[];
    formats: IRFormatTypeSignature[];
    lpacks: IRLambdaParameterPackTypeSignature[];

    errInfos: { file: string, sinfo: IRSourceInfo, kind: "arith" | "runtime" | "userspec", checkID: number }[];
    errCtr: number;

    currentFile: string | undefined;

    isTaskAllowed: boolean = false;
    currentReturnType: TypeSignature | undefined;
    currentImplicitReturnVar: string | undefined;
    currentPostconditions: PostConditionDecl[] | undefined

    currentTypeInstantiation: TypeInstantiationInfo | undefined;
    currentInvokeInstantation: InvokeInstantiationInfo | undefined;

    pendingblocks: IRStatement[][];
    rescopeStack: Map<string, string>[]; //Maps from old name to new name
    tmpVarCtr: number;

    constructor(assembly: Assembly, generateTestInfo: boolean, testfilefilter: string[] | undefined, testfilters: TestAssociation[] | undefined) {
        this.assembly = assembly;
        this.generateTestInfo = generateTestInfo;
        this.testfilefilter = testfilefilter;
        this.testfilters = testfilters;
        
        this.regexs = [];
        this.elists = [];
        this.dashtypes = [];
        this.formats = [];
        this.lpacks = [];

        this.errInfos = [];
        this.errCtr = 0;

        this.pendingblocks = [];
        this.rescopeStack = [];
        this.tmpVarCtr = 0;
    }

    private initCodeProcessingContext(file: string, isTaskAllowed: boolean, rtype: TypeSignature, implicitreturn: string | undefined, postconds: PostConditionDecl[] | undefined, typeinst: TypeInstantiationInfo | undefined, invokeinst: InvokeInstantiationInfo | undefined) {
        this.currentFile = file;
        this.isTaskAllowed = isTaskAllowed;
        this.currentReturnType = rtype;
        this.currentImplicitReturnVar = implicitreturn;
        this.currentPostconditions = postconds;

        this.currentTypeInstantiation = typeinst;
        this.currentInvokeInstantation = invokeinst;

        this.pendingblocks = [];
        this.rescopeStack = [];
        this.tmpVarCtr = 0;
    }

    private convertSourceInfo(sinfo: SourceInfo): IRSourceInfo {
        return new IRSourceInfo(sinfo.line, sinfo.column);
    }

    private registerError(file: string, sinfo: IRSourceInfo, kind: "arith" | "runtime" | "userspec"): number {
        this.errInfos.push({ file: file, sinfo: sinfo, kind: kind, checkID: this.errCtr });
        return this.errCtr++;
    }

    private generateLocalTemplateMapping(tnames: string[], terms: TypeSignature[]): TemplateNameMapper | undefined {
        assert(terms.length === tnames.length);

        if(terms.length === 0) {
            return undefined;
        }

        let tmap = new Map<string, TypeSignature>();
        tnames.forEach((t, ii) => {
            tmap.set(t, terms[ii]);
        });

        return TemplateNameMapper.createInitialMapping(tmap);
    }

    private applyLocalTemplateMapping(tsig: TypeSignature, mapper: TemplateNameMapper | undefined): TypeSignature {
        return mapper !== undefined ? tsig.remapTemplateBindings(mapper) : tsig;
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
        const bb = this.pendingblocks.pop() as IRStatement[];

        const abortidx = bb.findIndex((stmt) => stmt instanceof IRAbortStatement);
        if(abortidx === -1 || abortidx < bb.length - 1) {
            return bb;
        }
        else {
            return bb.slice(0, abortidx + 1);
        }
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

    private tproc(ttype: TypeSignature): TypeSignature {
        if(this.currentInvokeInstantation !== undefined) {
            return this.currentInvokeInstantation.binds !== undefined ? ttype.remapTemplateBindings(this.currentInvokeInstantation.binds) : ttype;
        }
        else if(this.currentTypeInstantiation !== undefined) {
            return this.currentTypeInstantiation.binds !== undefined ? ttype.remapTemplateBindings(this.currentTypeInstantiation.binds) : ttype;
        }
        else {
            return ttype;
        }
    }

    private processTypeSignature(tsig: TypeSignature): IRTypeSignature {
        let rtsig: TypeSignature = this.tproc(tsig);

        if(rtsig instanceof VoidTypeSignature) {
            return new IRVoidTypeSignature();
        }
        else if(rtsig instanceof NominalTypeSignature) {
            return new IRNominalTypeSignature(rtsig.tkeystr);
        }
        else if(rtsig instanceof EListTypeSignature) {
            const elisttsig = rtsig as EListTypeSignature;
            const irents = elisttsig.entries.map<IRTypeSignature>((ent) => this.processTypeSignature(ent));

            if(this.elists.find((el) => el.tkeystr === rtsig.tkeystr) === undefined) {
                this.elists.push(new IREListTypeSignature(rtsig.tkeystr, irents));
            }

            return new IREListTypeSignature(rtsig.tkeystr, irents);
        }
        else if(rtsig instanceof DashResultTypeSignature) {
            const drtsig = rtsig as DashResultTypeSignature;
            const irents = drtsig.entries.map<IRTypeSignature>((ent) => this.processTypeSignature(ent));

            if(this.dashtypes.find((el) => el.tkeystr === rtsig.tkeystr) === undefined) {
                this.dashtypes.push(new IRDashResultTypeSignature(rtsig.tkeystr, irents));
            }

            return new IRDashResultTypeSignature(rtsig.tkeystr, irents);
        }
        else if(rtsig instanceof FormatStringTypeSignature) {
            const ffmtsig = rtsig as FormatStringTypeSignature;
            const irfmts = ffmtsig.terms.map<{argname: string, argtype: IRTypeSignature}>((term) => {
                return {argname: term.argname, argtype: this.processTypeSignature(term.argtype)};
            });

            let fsig: IRFormatTypeSignature;
            if(ffmtsig.oftype === "CString") {
                fsig = new IRFormatCStringTypeSignature(rtsig.tkeystr, this.processTypeSignature(ffmtsig.rtype), irfmts);
            }
            else {
                fsig = new IRFormatStringTypeSignature(rtsig.tkeystr, this.processTypeSignature(ffmtsig.rtype), irfmts);
            }

            if(this.formats.find((el) => el.tkeystr === rtsig.tkeystr) === undefined) {
                this.formats.push(fsig);
            }
            return fsig;
        }
        else if(rtsig instanceof FormatPathTypeSignature) {
            const fpathtsig = rtsig as FormatPathTypeSignature;
            const irfmts = fpathtsig.terms.map<{argname: string, argtype: IRTypeSignature}>((term) => {
                return {argname: term.argname, argtype: this.processTypeSignature(term.argtype)};
            });

            let fsig: IRFormatTypeSignature;
            if(fpathtsig.oftype === "Path") {
                fsig = new IRFormatPathTypeSignature(rtsig.tkeystr, this.processTypeSignature(fpathtsig.rtype), irfmts);
            }
            else if(fpathtsig.oftype === "PathFragment") {
                fsig = new IRFormatPathFragmentTypeSignature(rtsig.tkeystr, this.processTypeSignature(fpathtsig.rtype), irfmts);
            }
            else {
                fsig = new IRFormatPathGlobTypeSignature(rtsig.tkeystr, this.processTypeSignature(fpathtsig.rtype), irfmts);
            }

            if(this.formats.find((el) => el.tkeystr === rtsig.tkeystr) === undefined) {
                this.formats.push(fsig);
            }
            return fsig;
        }
        else {
            assert(false, `ASMToIRConverter: Unsupported type signature -- ${rtsig.tkeystr}`);
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

    //If we flatten an expression but it is nested then we need to simplify it -- this handles that by creating temps!
    private makeExpressionImmediate(exp: IRExpression, oftype: TypeSignature): IRImmediateExpression {
        if(exp instanceof IRImmediateExpression) {
            return exp;
        }
        else {
            if(exp instanceof IRSimpleExpression) {
                const irtype = this.processTypeSignature(oftype);
                const tmpname = this.generateTempVarName();
                this.pushStatement(new IRTempAssignExpressionStatement(tmpname, exp, irtype));

                return new IRAccessTempVariableExpression(tmpname);
            }
            else {
                return this.makeExpressionSimple(exp, oftype) as IRAccessTempVariableExpression;
            }
        }
    }

    private coerceToBoolForTest(exp: IRSimpleExpression, oftype: TypeSignature): IRSimpleExpression {
        if(oftype.tkeystr === "Bool") {
            return exp;
        }
        else {
            //TODO: check if this is a literal typedecl true/false and optimize

            return new IRAccessTypeDeclValueExpression(this.processTypeSignature(oftype), exp);
        }
    }

    private makeCoercionExplicitAsNeeded(exp: IRSimpleExpression, fromtype: TypeSignature, totype: TypeSignature): IRSimpleExpression {
        const ftype = this.tproc(fromtype);
        const ttype = this.tproc(totype);

        if(ftype.tkeystr === ttype.tkeystr) {
            return exp;
        }
        else {
            assert(ftype instanceof NominalTypeSignature, "ASMToIRConverter::makeCoercionExplicitAsNeeded - fromtype not nominal");
            assert(ttype instanceof NominalTypeSignature, "ASMToIRConverter::makeCoercionExplicitAsNeeded - totype not nominal");

            if(ftype.decl instanceof AbstractConceptTypeDecl) {
                return new IRWidenConceptRepresentationExpression(this.processTypeSignature(ftype), this.processTypeSignature(ttype), exp);
            }
            else {
                if(ftype.tkeystr === "None") {
                    return new IRLiteralOptionOfNoneExpression(this.processTypeSignature(ttype));
                }
                else if(ftype.decl instanceof SomeTypeDecl) {
                    return new IRConstructOptionFromSomeExpression(this.processTypeSignature(ttype), this.processTypeSignature(ftype), exp);
                }
                else if(ftype.decl instanceof OkTypeDecl) {
                    return new IRConstructResultFromOkExpression(this.processTypeSignature(ttype), this.processTypeSignature(ftype), exp);
                }
                else if(ftype.decl instanceof FailTypeDecl) {
                    return new IRConstructResultFromFailExpression(this.processTypeSignature(ttype), this.processTypeSignature(ftype), exp);
                }
                else {
                    return new IRBoxEntityToConceptRepresentationExpression(this.processTypeSignature(ttype), this.processTypeSignature(ftype), exp);
                }
            }
        }
    }

    private static isLiteralFalseExpression(exp: IRExpression): boolean {
        //TODO: can make this work with literal typedecls too
        return exp instanceof IRLiteralBoolExpression && exp.value === false;
    }

    private static isLiteralTrueExpression(exp: IRExpression): boolean {
        //TODO: can make this work with literal typedecls too
        return exp instanceof IRLiteralBoolExpression && exp.value === true;
    }

    private getSpecialType(tname: string): IRTypeSignature {
        return new IRNominalTypeSignature(tname);
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

                return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenCallRefVariableExpression(crexp), this.tproc(crexp.getType())), this.tproc(crexp.getType()));
            }
            case ExpressionTag.CallRefThisExpression: {
                const crexp = exp as CallRefThisExpression;
                
                return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenCallRefThisExpression(crexp), this.tproc(crexp.getType())), this.tproc(crexp.getType()));
            }
            case ExpressionTag.CallRefSelfExpression: {
                const crexp = exp as CallRefSelfExpression;

                return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenCallRefSelfExpression(crexp), this.tproc(crexp.getType())), this.tproc(crexp.getType()));
            }
            case ExpressionTag.CallTaskActionExpression: {
                const crexp = exp as CallTaskActionExpression;
                
                return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenCallTaskActionExpression(crexp), this.tproc(crexp.getType())), this.tproc(crexp.getType()));
            }
            default: {
                const ttag = exp.tag;

                if(ttag === ExpressionTag.CallNamespaceFunctionExpression) {
                    const crexp = exp as CallNamespaceFunctionExpression;

                    return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenCallNamespaceFunctionExpression(crexp), this.tproc(crexp.getType())), this.tproc(crexp.getType()));
                }
                else if(ttag === ExpressionTag.CallTypeFunctionExpression) {
                    const crexp = exp as CallTypeFunctionExpression;

                    return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenCallTypeFunctionExpression(crexp), this.tproc(crexp.getType())), this.tproc(crexp.getType()));
                }
                else if(ttag === ExpressionTag.LambdaInvokeExpression) {
                    const crexp = exp as LambdaInvokeExpression;

                    return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenLambdaInvokeExpression(crexp), this.tproc(crexp.getType())), this.tproc(crexp.getType()));
                }
                else if(ttag === ExpressionTag.PostfixOpExpression) {
                    const crexp = exp as PostfixOp;

                    return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenPostfixOp(crexp), this.tproc(crexp.getType())), this.tproc(crexp.getType()));
                }
                else if(ttag === ExpressionTag.PrefixNotOpExpression) {
                    const nexp = exp as PrefixNotOpExpression;
                    const nval = this.coerceToBoolForTest(this.flattenITestGuardExpression(nexp.exp), this.tproc(nexp.exp.getType()));

                    if(ASMToIRConverter.isLiteralTrueExpression(nval)) {
                        return new IRLiteralBoolExpression(false);
                    }
                    else if(ASMToIRConverter.isLiteralFalseExpression(nval)) {
                        return new IRLiteralBoolExpression(true);
                    }
                    else {
                        return new IRPrefixNotOpExpression(nval, this.getSpecialType("Bool"));
                    }
                }
                else if(ttag === ExpressionTag.LogicAndExpression) {
                    const aexps = (exp as LogicAndExpression).exps.map((e) => this.coerceToBoolForTest(this.flattenITestGuardExpression(e), this.tproc(e.getType())));
                    
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
                    return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenExpression(exp), this.tproc(exp.getType())), this.tproc(exp.getType()));
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
        const hastemplate = exp.terms.length > 0;
        const haslambda = exp.args.args.some((arg) => (arg instanceof StdArgumentValue) && arg.exp.getType() instanceof LambdaTypeSignature);
        const fdecl = this.assembly.resolveNamespaceFunction(exp.ns, exp.name, hastemplate, haslambda, exp.args.hasSpecialRef()) as NamespaceFunctionDecl;

        const haspreconds = fdecl.preconditions.length > 0;
        const imapper = this.generateLocalTemplateMapping(fdecl.terms.map((t) => t.name), exp.terms);

        const aargs: IRSimpleExpression[] = [];
        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            const ii = exp.shuffleinfo[i];
            const pinfo = fdecl.params[i];
            const ftype = this.applyLocalTemplateMapping(pinfo.type, imapper);
            
            if(ii[0] === -1) {
                const crexp = this.assembly.tryReduceConstantExpression(pinfo.optDefaultValue as Expression);

                if(crexp !== undefined) {
                    const sexp = this.flattenExpression(crexp);
                    const cexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(sexp, crexp.getType()), crexp.getType(), ftype);

                    const fexp = haspreconds ? this.makeExpressionImmediate(cexp, ftype) : cexp;
                    aargs.push(fexp);
                }
                else {
                    assert(false, "ASMToIRConverter::flattenCallNamespaceFunctionExpression - Invoke computation for default argument not implemented");
                }
            }
            else {
                const eexp = exp.args.args[ii[0]] as StdArgumentValue;
                const sexp = this.flattenExpression(eexp.exp);
                const cexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(sexp, eexp.exp.getType()), eexp.exp.getType(), ftype);

                const fexp = haspreconds ? this.makeExpressionImmediate(cexp, ftype) : cexp;
                aargs.push(fexp);
            }
        }

        //do rest parameter as needed
        if(exp.resttype !== undefined) {
            assert(false, "rest parameters not yet implemented in flattenCallNamespaceFunctionExpression");
        }

        //do preconditions as needed
        for(let i = 0; i < fdecl.preconditions.length; ++i) {
            const invdecl = fdecl.preconditions[i];
            
            this.pushStatement(new IRPreconditionCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.diagnosticTag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), exp.monomorhphizedkey as string, invdecl.ii, aargs));
        }

        if(!exp.args.hasSpecialRef()) {
            return new IRInvokeSimpleExpression(exp.monomorhphizedkey as string, aargs);
        }
        else {
            const srpos = exp.shuffleinfo.findIndex((si) => exp.args.args[si[0]] instanceof PassingArgumentValue);
            const ii = exp.shuffleinfo[srpos][0];
            const passarg = exp.args.args[ii] as PassingArgumentValue;
            const ivar = (passarg.exp as AccessVariableExpression).srcname;
            const ivartype = this.processTypeSignature((passarg.exp as AccessVariableExpression).getType());
            
            return new IRInvokeSimpleWithImplicitsExpression(exp.monomorhphizedkey as string, aargs, ii, ivar, ivartype, passarg.kind);
        }
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

    private needsAddCheck(opchk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float"): boolean {
        if(opchk === "ChkNat" || opchk === "ChkInt") {
            return false;
        }

        return true;
    }

    private needsSubCheck(opchk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float"): boolean {
        if(opchk === "ChkInt") {
            return false;
        }

        return true;
    }

    private needsMultCheck(opchk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float"): boolean {
        if(opchk === "ChkNat" || opchk === "ChkInt") {
            return false;
        }

        return true;
    }

    private needsDivCheck(rhs: Expression, opchk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float"): boolean {
        if(!(rhs instanceof LiteralSimpleExpression)) {
            return true;
        }

        const rval = (rhs as LiteralSimpleExpression).value;
        if(opchk === "Nat") {
            return /[+-]?0n/.test(rval);
        }
        else if(opchk === "Int") {
            return /[+-]?0i/.test(rval);
        }
        else if(opchk === "ChkNat") {
            return /[+-]?0N/.test(rval);
        }
        else if(opchk === "ChkInt") {
            return /[+-]?0I/.test(rval);
        }
        else if(opchk === "Float") {
            return /[+-]?0\.0+f/.test(rval);
        }
        else {
            return true;
        }
    }

    private flattenListConstructor(decl: ListTypeDecl, exp: ConstructorPrimaryExpression): IRSimpleExpression {
        const tcons = this.tproc(exp.ctype) as NominalTypeSignature;
        
        if(exp.args.args.length === 0) {
            return new IRConstructorListEmptyExpression(this.processTypeSignature(tcons));
        }
        else {
            if(exp.args.args.every((a) => a instanceof PositionalArgumentValue)) {
                const aargs: IRSimpleExpression[] = [];
                for(let i = 0; i < exp.args.args.length; ++i) {
                    const eexp = exp.args.args[i] as PositionalArgumentValue;
                    const sexp = this.flattenExpression(eexp.exp);
                    const cexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(sexp, eexp.exp.getType()), eexp.exp.getType(), tcons.alltermargs[0]);

                    aargs.push(cexp);
                }

                return new IRConstructorListSingletonsExpression(this.processTypeSignature(tcons), aargs);
            }
            else {
                assert(false, "ASMToIRConverter::flattenListConstructor - spread and mixed args not implemented");
            }
        }
    }

    private flattenCollectionConstructor(cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): IRSimpleExpression {
        if(cdecl instanceof ListTypeDecl) {
            return this.flattenListConstructor(cdecl, exp);
        }
        else {
            assert(false, "ASMToIRConverter::flattenCollectionConstructor - Not Implemented");
        }
    }
    
    private flattenStandardConstructor(decl: AbstractEntityTypeDecl, exp: ConstructorPrimaryExpression): IRSimpleExpression {
        const hasinvchks = decl.allInvariants.length !== 0;
        const bfinfo = decl.saturatedBFieldInfo;

        const tcons = this.tproc(exp.ctype) as NominalTypeSignature;
        const imapper = this.generateLocalTemplateMapping(decl.terms.map((t) => t.name), tcons.alltermargs);

        const aargs: IRSimpleExpression[] = [];
        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            const ii = exp.shuffleinfo[i];
            const finfo = bfinfo[i];
            const ftype = this.applyLocalTemplateMapping(finfo.type, imapper);
            
            if(ii[0] === -1) {
                const eexp = this.assembly.resolveFieldDeclDefaultExpFromTypeSignature(finfo.containingtype, finfo.name) as Expression;
                const crexp = eexp !== undefined ? this.assembly.tryReduceConstantExpression(eexp) : undefined;

                if(crexp !== undefined) {
                    const sexp = this.flattenExpression(crexp);
                    const cexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(sexp, crexp.getType()), crexp.getType(), ftype);

                    const fexp = hasinvchks ? this.makeExpressionImmediate(cexp, ftype) : cexp;
                    aargs.push(fexp);
                }
                else {
                    assert(false, "ASMToIRConverter::flattenStandardConstructor - Invoke computation for default argument not implemented");
                }
            }
            else {
                const eexp = exp.args.args[ii[0]] as StdArgumentValue;
                const sexp = this.flattenExpression(eexp.exp);
                const cexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(sexp, eexp.exp.getType()), eexp.exp.getType(), ftype);

                const fexp = hasinvchks ? this.makeExpressionImmediate(cexp, ftype) : cexp;
                aargs.push(fexp);
            }
        }

        //do invariants as needed (on appropriate sets of args
        for(let i = 0; i < decl.allInvariants.length; ++i) {
            const invdecl = decl.allInvariants[i];
            
            const ffargnames = (invdecl.containingtype as NominalTypeSignature).decl.saturatedBFieldInfo.map<string>((bf) => bf.name);
            const args: IRImmediateExpression[] = ffargnames.map<IRImmediateExpression>((aname) => {
                const aaidx = bfinfo.findIndex((bf) => bf.name === aname);
                assert(aaidx !== -1, "invariant arg name not found in field list");

                return aargs[aaidx] as IRImmediateExpression;
            });

            this.pushStatement(new IREntityInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, args));
        }

        return new IRConstructorStandardEntityExpression(this.processTypeSignature(exp.ctype), aargs);
    }

    private flattenSpecialConstructableConstructor(cdecl: ConstructableTypeDecl, exp: ConstructorPrimaryExpression): IRSimpleExpression {
        const ctype = this.tproc(exp.ctype) as NominalTypeSignature;

        if(cdecl instanceof OkTypeDecl) {
            const argt = this.tproc((exp.args.args[0] as StdArgumentValue).exp.getType());
            const arg = this.makeExpressionSimple(this.flattenExpression((exp.args.args[0] as StdArgumentValue).exp), argt);
            const targ = this.makeCoercionExplicitAsNeeded(arg, argt, ctype.alltermargs[0]);

            return new IRConstructorOkTypeExpression(this.processTypeSignature(ctype), targ);
        }
        else if(cdecl instanceof FailTypeDecl) {
            const argt = this.tproc((exp.args.args[0] as StdArgumentValue).exp.getType());
            const arg = this.makeExpressionSimple(this.flattenExpression((exp.args.args[0] as StdArgumentValue).exp), argt);
            const targ = this.makeCoercionExplicitAsNeeded(arg, argt, ctype.alltermargs[1]);

            return new IRConstructorFailTypeExpression(this.processTypeSignature(ctype), targ);
        }
        else if((cdecl instanceof APIErrorTypeDecl) || (cdecl instanceof APIRejectedTypeDecl) || (cdecl instanceof APIDeniedTypeDecl) || (cdecl instanceof APIFlaggedTypeDecl) || (cdecl instanceof APISuccessTypeDecl)) {
            assert(false, "ASMToIRConverter::flattenSpecialConstructableConstructor - Not Implemented");
        }
        else if(cdecl instanceof SomeTypeDecl) {
            const argt = this.tproc((exp.args.args[0] as StdArgumentValue).exp.getType());
            const arg = this.makeExpressionSimple(this.flattenExpression((exp.args.args[0] as StdArgumentValue).exp), argt);
            const targ = this.makeCoercionExplicitAsNeeded(arg, argt, ctype.alltermargs[0]);

            return new IRConstructorSomeTypeExpression(this.processTypeSignature(ctype), targ);
        }
        else {
            const kargt = this.tproc((exp.args.args[0] as StdArgumentValue).exp.getType());
            const karg = this.makeExpressionSimple(this.flattenExpression((exp.args.args[0] as StdArgumentValue).exp), kargt);
            const ktarg = this.makeCoercionExplicitAsNeeded(karg, kargt, ctype.alltermargs[0]);

            const vargt = this.tproc((exp.args.args[1] as StdArgumentValue).exp.getType());
            const varg = this.makeExpressionSimple(this.flattenExpression((exp.args.args[1] as StdArgumentValue).exp), vargt);
            const vtarg = this.makeCoercionExplicitAsNeeded(varg, vargt, ctype.alltermargs[1]);

            return new IRConstructorMapEntryTypeExpression(this.processTypeSignature(ctype), ktarg, vtarg);
        }
    }

    private flattenSpecialTypeDeclConstructor(cdecl: TypedeclTypeDecl, exp: ConstructorPrimaryExpression): IRSimpleExpression {
        const ctype = this.tproc(exp.ctype) as NominalTypeSignature;
        const tdecl = ctype.decl as TypedeclTypeDecl;

        const cargt = this.tproc((exp.args.args[0] as StdArgumentValue).exp.getType());
        let cval = this.makeExpressionSimple(this.flattenExpression((exp.args.args[0] as StdArgumentValue).exp), cargt);
        
        if(tdecl.allInvariants.length !== 0 || tdecl.optofexp !== undefined || tdecl.optsizerng !== undefined) {
            cval = this.makeExpressionImmediate(cval, tdecl.valuetype);
        }

        if(tdecl.optsizerng !== undefined) {
            if(tdecl.valuetype.tkeystr === "CString") {
                this.pushStatement(new IRTypeDeclSizeRangeCheckCStringStatement(tdecl.file, this.convertSourceInfo(tdecl.sinfo), this.registerError(tdecl.file, this.convertSourceInfo(tdecl.sinfo), "userspec"), tdecl.optsizerng.min, tdecl.optsizerng.max, cval as IRImmediateExpression));
            }
            else {
                this.pushStatement(new IRTypeDeclSizeRangeCheckUnicodeStringStatement(tdecl.file, this.convertSourceInfo(tdecl.sinfo), this.registerError(tdecl.file, this.convertSourceInfo(tdecl.sinfo), "userspec"), tdecl.optsizerng.min, tdecl.optsizerng.max, cval as IRImmediateExpression));
            }
        }

        if(tdecl.optofexp !== undefined) {
            if(tdecl.valuetype.tkeystr === "CString") {
                const regex = this.flattenExpression(tdecl.optofexp) as IRLiteralCRegexExpression;
                this.pushStatement(new IRTypeDeclFormatCheckCStringStatement(tdecl.file, this.convertSourceInfo(tdecl.sinfo), this.registerError(tdecl.file, this.convertSourceInfo(tdecl.sinfo), "userspec"), regex, cval as IRImmediateExpression));
            }
            else {
                const regex = this.flattenExpression(tdecl.optofexp) as IRLiteralUnicodeRegexExpression;
                this.pushStatement(new IRTypeDeclFormatCheckUnicodeStringStatement(tdecl.file, this.convertSourceInfo(tdecl.sinfo), this.registerError(tdecl.file, this.convertSourceInfo(tdecl.sinfo), "userspec"), regex, cval as IRImmediateExpression));
            }
        }

        if(tdecl.allInvariants.length !== 0) {
            const invchecks = tdecl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, cval);
            });
                
            this.pushStatements(invchecks);
        }

        return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(ctype), cval);
    }

    private flattenConstructorPrimaryExpression(exp: ConstructorPrimaryExpression): IRSimpleExpression {
        const tsig = this.tproc(exp.ctype) as NominalTypeSignature;
        const decl = tsig.decl;

        if(decl instanceof AbstractCollectionTypeDecl) {
            return this.flattenCollectionConstructor(decl, exp);
        }
        else if(decl instanceof ConstructableTypeDecl) {
            return this.flattenSpecialConstructableConstructor(decl, exp);
        }
        else if(decl instanceof TypedeclTypeDecl) {
            return this.flattenSpecialTypeDeclConstructor(decl, exp);
        }
        else {
            assert(decl instanceof AbstractEntityTypeDecl, "Expected AbstractEntityTypeDecl in flattenConstructorPrimaryExpression");
            return this.flattenStandardConstructor(decl as AbstractEntityTypeDecl, exp);
        }
    }

    private flattenSpecialConstructorExpression(exp: SpecialConstructorExpression): IRSimpleExpression {
        const ctype = this.tproc(exp.constype as TypeSignature) as NominalTypeSignature;

        const argt = this.tproc(exp.arg.getType());
        const arg = this.makeExpressionSimple(this.flattenExpression(exp.arg), argt);
            
        if(exp.rop === "some") {
            const targ = this.makeCoercionExplicitAsNeeded(arg, argt, ctype.alltermargs[0]);
            return new IRConstructorSomeTypeExpression(this.processTypeSignature(ctype), targ);
        }
        else if(exp.rop === "ok") {
            const targ = this.makeCoercionExplicitAsNeeded(arg, argt, ctype.alltermargs[0]);
            return new IRConstructorOkTypeExpression(this.processTypeSignature(ctype), targ);
        }
        else {
            //fail
            const targ = this.makeCoercionExplicitAsNeeded(arg, argt, ctype.alltermargs[1]);
            return new IRConstructorFailTypeExpression(this.processTypeSignature(ctype), targ);
        }
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
            return new IRLiteralNatExpression((exp as LiteralSimpleExpression).value.slice(0, -1));
        }
        else if(ttag === ExpressionTag.LiteralIntExpression) {
            return new IRLiteralIntExpression((exp as LiteralSimpleExpression).value.slice(0, -1));
        }
        else if(ttag === ExpressionTag.LiteralChkNatExpression) {
            const ll = (exp as LiteralSimpleExpression).value;
            return new IRLiteralChkNatExpression(ll === "ChkNat::npos" ? ll : ll.slice(0, -1));
        }
        else if(ttag === ExpressionTag.LiteralChkIntExpression) {
            const ll = (exp as LiteralSimpleExpression).value;
            return new IRLiteralChkIntExpression(ll === "ChkInt::npos" ? ll : ll.slice(0, -1));
        }
        else if(ttag === ExpressionTag.LiteralRationalExpression) {
            const rrval = (exp as LiteralSimpleExpression).value;
            const slpos = rrval.indexOf("/");
            
            return new IRLiteralRationalExpression(rrval.slice(0, slpos), rrval.slice(slpos + 1, -1));
        }
        else if(ttag === ExpressionTag.LiteralFloatExpression) {
            return new IRLiteralFloatExpression((exp as LiteralSimpleExpression).value.slice(0, -1));
        }
        else if(ttag === ExpressionTag.LiteralDecimalExpression) {
            return new IRLiteralDecimalExpression((exp as LiteralSimpleExpression).value.slice(0, -1));
        }
        else if(ttag === ExpressionTag.LiteralDecimalDegreeExpression) {
            return new IRLiteralDecimalDegreeExpression((exp as LiteralSimpleExpression).value.slice(0, -2));
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
                    return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, iexp);
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
                    return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, iexp);
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
                    return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, iexp);
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
                    this.pushStatement(new IRPreconditionCheckStatement(this.currentFile as string, this.convertSourceInfo(exp.sinfo), undefined, this.registerError(this.currentFile as string, this.convertSourceInfo(exp.sinfo), "runtime"), "env::get", 0, [new IRAccessEnvHasExpression(kbytes)]));
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
                const flatconstname = `${tnsa.ns.emit()}::${tnsa.name}`;
                return new IRAccessConstantExpression(flatconstname);
            }
        }
        else if(ttag === ExpressionTag.AccessStaticFieldExpression) {
            const tasf = exp as AccessStaticFieldExpression;
            const rvv = this.assembly.tryReduceConstantExpression(tasf);
            if(rvv !== undefined) {
                return this.flattenExpression(rvv);
            }
            else {
                const flatfieldname = `${(tasf.resolvedDeclType as TypeSignature).emit()}::${tasf.name}`;
                return new IRAccessConstantExpression(flatfieldname);
            }
        }
        else if(ttag === ExpressionTag.AccessEnumExpression) {
            const taee = exp as AccessEnumExpression;
            return new IRAccessEnumExpression(taee.stype.tkeystr, taee.name);
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
            return this.flattenConstructorPrimaryExpression(exp as ConstructorPrimaryExpression);
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
            return this.flattenSpecialConstructorExpression(exp as SpecialConstructorExpression);
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
            const eetype = this.tproc(pfxnot.exp.getType()) as NominalTypeSignature;
            const nexp = this.makeExpressionSimple(this.flattenExpression(pfxnot.exp), eetype);
            
            if(!(eetype.decl instanceof TypedeclTypeDecl)) {
                if(nexp instanceof IRPrefixNotOpExpression) {
                    return nexp.exp; //!!e is e
                }
                else if(ASMToIRConverter.isLiteralTrueExpression(nexp)) {
                    return new IRLiteralBoolExpression(false); //do the literal negation
                }
                else if(ASMToIRConverter.isLiteralFalseExpression(nexp)) {
                    return new IRLiteralBoolExpression(true); //do the literal negation
                }
                else {
                    return new IRPrefixNotOpExpression(nexp, this.processTypeSignature(pfxnot.opertype as TypeSignature));
                }
            }
            else {
                //TODO: check for literal true/false and optimize

                const tdaccess = new IRAccessTypeDeclValueExpression(this.processTypeSignature(eetype), nexp);
                const bnotop = new IRPrefixNotOpExpression(tdaccess, this.processTypeSignature(pfxnot.opertype as TypeSignature));
                const notop = (eetype.decl.allInvariants.length !== 0) ? this.makeExpressionImmediate(bnotop, this.tproc(pfxnot.opertype as TypeSignature)) : bnotop;

                if(eetype.decl.allInvariants.length !== 0) {
                    const invchecks = eetype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, notop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(eetype), notop);
            }
        }
        else if(ttag === ExpressionTag.PrefixNegateOrPlusOpExpression) {
            const pfxneg = exp as PrefixNegateOrPlusOpExpression;
            const eetype = this.tproc(pfxneg.exp.getType()) as NominalTypeSignature;
            const nexp = this.makeExpressionSimple(this.flattenExpression(pfxneg.exp), eetype);
            
            if(!(eetype.decl instanceof TypedeclTypeDecl)) {
                return pfxneg.op === "-" ? new IRPrefixNegateOpExpression(nexp, this.processTypeSignature(pfxneg.opertype as TypeSignature)) : nexp;
            }
            else {
                const tdaccess = new IRAccessTypeDeclValueExpression(this.processTypeSignature(eetype), nexp);
                const bnsop = pfxneg.op === "-" ? new IRPrefixNegateOpExpression(tdaccess, this.processTypeSignature(pfxneg.opertype as TypeSignature)) : tdaccess;
                const nsop = (eetype.decl.allInvariants.length !== 0) ? this.makeExpressionImmediate(bnsop, this.tproc(pfxneg.opertype as TypeSignature)) : bnsop;

                if(eetype.decl.allInvariants.length !== 0) {
                    const invchecks = eetype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, nsop);
                    });
                
                    this.pushStatements(invchecks);
                }
                
                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(eetype), nsop);
            }
        }
        else if(ttag === ExpressionTag.BinAddExpression) {
            const binadd = exp as BinAddExpression;
            const finaltype = this.tproc(binadd.getType()) as NominalTypeSignature;
            const leetype = this.tproc(binadd.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(binadd.rhs.getType()) as NominalTypeSignature;
            
            let [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(binadd.lhs), this.flattenExpression(binadd.rhs), leetype, reetype);

            const opchk = (binadd.opertype as TypeSignature).tkeystr as "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float";
            const optype = this.tproc(binadd.opertype as TypeSignature);
            const iropttype = this.processTypeSignature(optype);

            if(this.needsAddCheck(opchk)) {
                lexp = this.makeExpressionImmediate(lexp, optype);
                rexp = this.makeExpressionImmediate(rexp, optype);
                
                this.pushStatement(new IRErrorAdditionBoundsCheckStatement(this.currentFile as string, binadd.sinfo, this.registerError(this.currentFile as string, binadd.sinfo, "arith"), lexp, rexp, opchk));
            }

            if(!(finaltype.decl instanceof TypedeclTypeDecl)) {
                return new IRBinAddExpression(lexp, rexp, iropttype);
            }
            else {
                const baddop = new IRBinAddExpression(lexp, rexp, iropttype);
                let addop = (finaltype.decl.allInvariants.length !== 0) ? this.makeExpressionImmediate(baddop, optype) : baddop;

                if(finaltype.decl.allInvariants.length !== 0) {
                    const invchecks = finaltype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, addop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(finaltype), addop);
            }
        }
        else if(ttag === ExpressionTag.BinSubExpression) {
            const binsub = exp as BinSubExpression;
            const finaltype = this.tproc(binsub.getType()) as NominalTypeSignature;
            const leetype = this.tproc(binsub.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(binsub.rhs.getType()) as NominalTypeSignature;
            
            let [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(binsub.lhs), this.flattenExpression(binsub.rhs), leetype, reetype);

            const opchk = (binsub.opertype as TypeSignature).tkeystr as "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float";
            const optype = this.tproc(binsub.opertype as TypeSignature);
            const iropttype = this.processTypeSignature(optype);

            if(this.needsSubCheck(opchk)) {
                lexp = this.makeExpressionImmediate(lexp, optype);
                rexp = this.makeExpressionImmediate(rexp, optype);
                this.pushStatement(new IRErrorSubtractionBoundsCheckStatement(this.currentFile as string, this.convertSourceInfo(binsub.sinfo), this.registerError(this.currentFile as string, this.convertSourceInfo(binsub.sinfo), (opchk === "Nat" || opchk === "ChkNat") ? "runtime" : "arith"), lexp, rexp, opchk));
            }
            
            if(!(finaltype.decl instanceof TypedeclTypeDecl)) {
                return new IRBinSubExpression(lexp, rexp, iropttype);
            }
            else {
                const bsubop = new IRBinSubExpression(lexp, rexp, iropttype);
                let subop = (finaltype.decl.allInvariants.length !== 0) ? this.makeExpressionImmediate(bsubop, optype) : bsubop;

                if(finaltype.decl.allInvariants.length !== 0) {
                    const invchecks = finaltype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, subop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(finaltype), subop);
            }
        }
        else if(ttag === ExpressionTag.BinMultExpression) {
            const binmult = exp as BinMultExpression;
            const finaltype = this.tproc(binmult.getType()) as NominalTypeSignature;
            const leetype = this.tproc(binmult.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(binmult.rhs.getType()) as NominalTypeSignature;
            
            let [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(binmult.lhs), this.flattenExpression(binmult.rhs), leetype, reetype);

            const opchk = (binmult.opertype as TypeSignature).tkeystr as "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float";
            const optype = this.tproc(binmult.opertype as TypeSignature);
            const iropttype = this.processTypeSignature(optype);

            if(this.needsMultCheck(opchk)) {
                lexp = this.makeExpressionImmediate(lexp, optype);
                rexp = this.makeExpressionImmediate(rexp, optype);
                this.pushStatement(new IRErrorMultiplicationBoundsCheckStatement(this.currentFile as string, this.convertSourceInfo(binmult.sinfo), this.registerError(this.currentFile as string, this.convertSourceInfo(binmult.sinfo), "arith"), lexp, rexp, opchk));
            }
            
            if(!(finaltype.decl instanceof TypedeclTypeDecl)) {
                return new IRBinMultExpression(lexp, rexp, this.processTypeSignature(binmult.opertype as TypeSignature));
            }
            else {
                const bmultop = new IRBinMultExpression(lexp, rexp, iropttype);
                let multop = (finaltype.decl.allInvariants.length !== 0) ? this.makeExpressionImmediate(bmultop, optype) : bmultop;

                if(finaltype.decl.allInvariants.length !== 0) {
                    const invchecks = finaltype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, multop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(finaltype), multop);
            }
        }
        else if(ttag === ExpressionTag.BinDivExpression) {
            const bindiv = exp as BinDivExpression;
            const finaltype = this.tproc(bindiv.getType()) as NominalTypeSignature;
            const leetype = this.tproc(bindiv.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(bindiv.rhs.getType()) as NominalTypeSignature;
            
            let [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(bindiv.lhs), this.flattenExpression(bindiv.rhs), leetype, reetype);

            const opchk = (bindiv.opertype as TypeSignature).tkeystr as "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float";
            const optype = this.tproc(bindiv.opertype as TypeSignature);
            const iropttype = this.processTypeSignature(optype);

            if(this.needsDivCheck(bindiv.rhs, opchk)) {
                lexp = this.makeExpressionImmediate(lexp, optype);
                rexp = this.makeExpressionImmediate(rexp, optype);
                this.pushStatement(new IRErrorDivisionByZeroCheckStatement(this.currentFile as string, this.convertSourceInfo(bindiv.sinfo), this.registerError(this.currentFile as string, this.convertSourceInfo(bindiv.sinfo), "runtime"), lexp, rexp, opchk));
            }
            
            if(!(finaltype.decl instanceof TypedeclTypeDecl)) {
                return new IRBinDivExpression(lexp, rexp, iropttype);
            }
            else {
                const bdivop = new IRBinDivExpression(lexp, rexp, iropttype);
                let divop = (finaltype.decl.allInvariants.length !== 0) ? this.makeExpressionImmediate(bdivop, optype) : bdivop;

                if(finaltype.decl.allInvariants.length !== 0) {
                    const invchecks = finaltype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                        return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, divop);
                    });
                
                    this.pushStatements(invchecks);
                }

                return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(finaltype), divop);
            }
        }
        else if(ttag === ExpressionTag.BinKeyEqExpression) {
            const kkop = exp as BinKeyEqExpression;

            if(kkop.operkind === "lhsnone") {
                const rhs = this.flattenExpression(kkop.rhs);
                return new IRIsNoneOptionExpression(rhs, this.processTypeSignature(kkop.rhs.getType()));
            }
            else if(kkop.operkind === "rhsnone") {
                const lhs = this.flattenExpression(kkop.lhs);
                return new IRIsNoneOptionExpression(lhs, this.processTypeSignature(kkop.lhs.getType()));
            }
            else if(kkop.operkind === "lhskeyeqoption") {
                const optexp = this.flattenExpression(kkop.lhs);
                const opttype = this.processTypeSignature(kkop.lhs.getType());
                const valexp = this.flattenExpression(kkop.rhs);
                const valuetype = this.processTypeSignature(kkop.rhs.getType());

                return new IRIsOptionEqValueExpression(optexp, opttype, valexp, valuetype);
            }
            else if(kkop.operkind === "rhskeyeqoption") {
                const optexp = this.flattenExpression(kkop.rhs);
                const opttype = this.processTypeSignature(kkop.rhs.getType());
                const valexp = this.flattenExpression(kkop.lhs);
                const valuetype = this.processTypeSignature(kkop.lhs.getType());

                return new IRIsOptionEqValueExpression(optexp, opttype, valexp, valuetype);
            }
            else if(kkop.operkind === "lhskeyeqsome") {
                const someexp = this.flattenExpression(kkop.lhs);
                const sometype = this.processTypeSignature(kkop.lhs.getType());
                const valexp = this.flattenExpression(kkop.rhs);
                const valuetype = this.processTypeSignature(kkop.rhs.getType());

                return new IRIsSomeEqValueExpression(someexp, sometype, valexp, valuetype);
            }
            else if(kkop.operkind === "rhskeyeqsome") {
                const someexp = this.flattenExpression(kkop.rhs);
                const sometype = this.processTypeSignature(kkop.rhs.getType());
                const valexp = this.flattenExpression(kkop.lhs);
                const valuetype = this.processTypeSignature(kkop.lhs.getType());

                return new IRIsSomeEqValueExpression(someexp, sometype, valexp, valuetype);
            }
            else {
                const lhs = this.flattenExpression(kkop.lhs);
                const rhs = this.flattenExpression(kkop.rhs);

                return new IRBinKeyEqDirectExpression(lhs, rhs, this.processTypeSignature(kkop.lhs.getType()));
            }
        }
        else if(ttag === ExpressionTag.BinKeyNeqExpression) {
            const kkop = exp as BinKeyNeqExpression;

            if(kkop.operkind === "lhsnone") {
                const rhs = this.flattenExpression(kkop.rhs);
                return new IRIsNotNoneOptionExpression(rhs, this.processTypeSignature(kkop.rhs.getType()));
            }
            else if(kkop.operkind === "rhsnone") {
                const lhs = this.flattenExpression(kkop.lhs);
                return new IRIsNotNoneOptionExpression(lhs, this.processTypeSignature(kkop.lhs.getType()));
            }
            else if(kkop.operkind === "lhskeyeqoption") {
                const optexp = this.flattenExpression(kkop.lhs);
                const opttype = this.processTypeSignature(kkop.lhs.getType());
                const valexp = this.flattenExpression(kkop.rhs);
                const valuetype = this.processTypeSignature(kkop.rhs.getType());

                return new IRIsOptionNeqValueExpression(optexp, opttype, valexp, valuetype);
            }
            else if(kkop.operkind === "rhskeyeqoption") {
                const optexp = this.flattenExpression(kkop.rhs);
                const opttype = this.processTypeSignature(kkop.rhs.getType());
                const valexp = this.flattenExpression(kkop.lhs);
                const valuetype = this.processTypeSignature(kkop.lhs.getType());

                return new IRIsOptionNeqValueExpression(optexp, opttype, valexp, valuetype);
            }
            else if(kkop.operkind === "lhskeyeqsome") {
                const someexp = this.flattenExpression(kkop.lhs);
                const sometype = this.processTypeSignature(kkop.lhs.getType());
                const valexp = this.flattenExpression(kkop.rhs);
                const valuetype = this.processTypeSignature(kkop.rhs.getType());

                return new IRIsSomeNeqValueExpression(someexp, sometype, valexp, valuetype);
            }
            else if(kkop.operkind === "rhskeyeqsome") {
                const someexp = this.flattenExpression(kkop.rhs);
                const sometype = this.processTypeSignature(kkop.rhs.getType());
                const valexp = this.flattenExpression(kkop.lhs);
                const valuetype = this.processTypeSignature(kkop.lhs.getType());

                return new IRIsSomeNeqValueExpression(someexp, sometype, valexp, valuetype);
            }
            else {
                const lhs = this.flattenExpression(kkop.lhs);
                const rhs = this.flattenExpression(kkop.rhs);

                return new IRBinKeyNeqDirectExpression(lhs, rhs, this.processTypeSignature(kkop.lhs.getType()));
            }
        }
        else if(ttag === ExpressionTag.KeyCompareEqExpression) {
            const kkop = exp as KeyCompareEqExpression;
            
            const lhs = this.flattenExpression(kkop.lhs);
            const rhs = this.flattenExpression(kkop.rhs);

            return new IRBinKeyEqDirectExpression(lhs, rhs, this.processTypeSignature(kkop.ktype));
        }
        else if(ttag === ExpressionTag.KeyCompareLessExpression) {
            const kklop = exp as KeyCompareLessExpression;
            
            const lhs = this.flattenExpression(kklop.lhs);
            const rhs = this.flattenExpression(kklop.rhs);

            return new IRBinKeyLessDirectExpression(lhs, rhs, this.processTypeSignature(kklop.ktype));
        }
        else if(ttag === ExpressionTag.NumericEqExpression) {
            const neqexp = exp as NumericEqExpression;
            const leetype = this.tproc(neqexp.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(neqexp.rhs.getType()) as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(neqexp.lhs), this.flattenExpression(neqexp.rhs), leetype, reetype);

            return new IRNumericEqExpression(lexp, rexp, this.processTypeSignature(neqexp.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericNeqExpression) {
            const nneqexp = exp as NumericNeqExpression;
            const leetype = this.tproc(nneqexp.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(nneqexp.rhs.getType()) as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(nneqexp.lhs), this.flattenExpression(nneqexp.rhs), leetype, reetype);

            return new IRNumericNeqExpression(lexp, rexp, this.processTypeSignature(nneqexp.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericLessExpression) {
            const nless = exp as NumericLessExpression;
            const leetype = this.tproc(nless.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(nless.rhs.getType()) as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(nless.lhs), this.flattenExpression(nless.rhs), leetype, reetype);

            return new IRNumericLessExpression(lexp, rexp, this.processTypeSignature(nless.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericLessEqExpression) {
            const nlesseq = exp as NumericLessEqExpression;
            const leetype = this.tproc(nlesseq.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(nlesseq.rhs.getType()) as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(nlesseq.lhs), this.flattenExpression(nlesseq.rhs), leetype, reetype);

            return new IRNumericLessEqExpression(lexp, rexp, this.processTypeSignature(nlesseq.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericGreaterExpression) {
            const ngreater = exp as NumericGreaterExpression;
            const leetype = this.tproc(ngreater.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(ngreater.rhs.getType()) as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(ngreater.lhs), this.flattenExpression(ngreater.rhs), leetype, reetype);

            return new IRNumericGreaterExpression(lexp, rexp, this.processTypeSignature(ngreater.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.NumericGreaterEqExpression) {
            const ngreatereq = exp as NumericGreaterEqExpression;
            const leetype = this.tproc(ngreatereq.lhs.getType()) as NominalTypeSignature;
            const reetype = this.tproc(ngreatereq.rhs.getType()) as NominalTypeSignature;
            
            const [lexp, rexp] = this.unwrapBinArgs(this.flattenExpression(ngreatereq.lhs), this.flattenExpression(ngreatereq.rhs), leetype, reetype);

            return new IRNumericGreaterEqExpression(lexp, rexp, this.processTypeSignature(ngreatereq.opertype as TypeSignature));
        }
        else if(ttag === ExpressionTag.LogicAndExpression) {
            const landexp = exp as LogicAndExpression;
            const landargs = landexp.exps.map<[IRExpression, IRTypeSignature]>((argexp) => [this.makeExpressionSimple(this.flattenExpression(argexp), this.tproc(argexp.getType()) as NominalTypeSignature), this.processTypeSignature(argexp.getType())]);

            if(landargs.some((a) => ASMToIRConverter.isLiteralFalseExpression(a[0]))) {
                //if one arg was a literal bool then the return must also be a bool type (namely false)
                return new IRLiteralBoolExpression(false);
            }
            else {
                let resbool: IRSimpleExpression;
                const filteredargs = landargs.filter((a) => !ASMToIRConverter.isLiteralTrueExpression(a[0]));
                if(filteredargs.length === 0) {
                    resbool = new IRLiteralBoolExpression(true); //all args were true
                }
                else if(filteredargs.length === 1) {
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

                if(this.tproc(exp.getType()).tkeystr === "Bool") {
                    return resbool;
                }
                else {
                    const baliastype = this.tproc(exp.getType()) as NominalTypeSignature;
                    const vtype = (baliastype.decl as TypedeclTypeDecl).valuetype;
                    resbool = baliastype.decl.allInvariants.length !== 0 ? this.makeExpressionImmediate(resbool, vtype) : resbool;

                    if(baliastype.decl.allInvariants.length !== 0) {
                        const invchecks = baliastype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                            return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, resbool);
                        });
                
                        this.pushStatements(invchecks);
                    }

                    return new IRConstructSafeTypeDeclExpression(this.processTypeSignature(exp.getType()), resbool);
                }
            }
        }
        else if(ttag === ExpressionTag.LogicOrExpression) {
            const lorexp = exp as LogicOrExpression;
            const lorargs = lorexp.exps.map<[IRExpression, IRTypeSignature]>((argexp) => [this.makeExpressionSimple(this.flattenExpression(argexp), this.tproc(argexp.getType()) as NominalTypeSignature), this.processTypeSignature(argexp.getType())]);

            if(lorargs.some((a) => ASMToIRConverter.isLiteralTrueExpression(a[0]))) {
                //if one arg was a literal bool then the return must also be a bool type (namely true)
                return new IRLiteralBoolExpression(true);
            }
            else {
                let resbool: IRSimpleExpression;
                const filteredargs = lorargs.filter((a) => !ASMToIRConverter.isLiteralFalseExpression(a[0]));
                if(filteredargs.length === 0) {
                    resbool = new IRLiteralBoolExpression(false); //all args were false
                }
                else if(filteredargs.length === 1) {
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

                if(this.tproc(exp.getType()).tkeystr === "Bool") {
                    return resbool;
                }
                else {
                    const baliastype = this.tproc(exp.getType()) as NominalTypeSignature;
                    const vtype = (baliastype.decl as TypedeclTypeDecl).valuetype;
                    resbool = baliastype.decl.allInvariants.length !== 0 ? this.makeExpressionImmediate(resbool, vtype) : resbool;
                    
                    if(baliastype.decl.allInvariants.length !== 0) {
                        const invchecks = baliastype.decl.allInvariants.map<IRTypeDeclInvariantCheckStatement>((invdecl) => {
                            return new IRTypeDeclInvariantCheckStatement(invdecl.file, this.convertSourceInfo(invdecl.sinfo), invdecl.tag, this.registerError(invdecl.file, this.convertSourceInfo(invdecl.sinfo), "userspec"), this.processTypeSignature(invdecl.containingtype).tkeystr, invdecl.ii, resbool);
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

            return this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenExpression(cle.exp), this.tproc(cle.exp.getType())), this.tproc(cle.exp.getType()));
        }
        else {
            const iiexp = exp as ChkLogicImpliesExpression;
            const renv = this.flattenITestGuardSet(iiexp.sinfo, iiexp.lhs);

            if(iiexp.bbinds.length === 0) {
                if(ASMToIRConverter.isLiteralFalseExpression(renv[0])) {
                    return new IRLiteralBoolExpression(true);
                }
                else {
                    this.pushStatementBlock();
                    const rhs = this.coerceToBoolForTest(this.makeExpressionSimple(this.flattenExpression(iiexp.rhs), this.tproc(iiexp.rhs.getType())), this.tproc(iiexp.rhs.getType()));
                    
                    const stmts = this.popStatementBlock();
                    if(stmts.length === 0) {
                        //no statements generated, so just return a simple expression directly
                        return new IRLogicOrExpression([new IRPrefixNotOpExpression(renv[0], this.getSpecialType("Bool")), rhs]);
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

        if(exp.bbinds.length === 0) {
            if(ASMToIRConverter.isLiteralTrueExpression(renv[0])) {
                return this.makeExpressionSimple(this.flattenExpression(exp.trueValue), this.tproc(exp.trueValue.getType()));
            }
            else if(ASMToIRConverter.isLiteralFalseExpression(renv[0])) {
                return this.makeExpressionSimple(this.flattenExpression(exp.falseValue), this.tproc(exp.falseValue.getType()));
            }
            else {
                this.pushStatementBlock();
                const texp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(this.flattenExpression(exp.trueValue), this.tproc(exp.trueValue.getType())), this.tproc(exp.trueValue.getType()), exp.rtype as TypeSignature);
                const fstmts = this.popStatementBlock();

                this.pushStatementBlock();
                const fexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(this.flattenExpression(exp.falseValue), this.tproc(exp.falseValue.getType())), this.tproc(exp.falseValue.getType()), exp.rtype as TypeSignature);
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
        else if(irval instanceof IRInvokeImplicitsExpression) {
            if(irvtype.tkeystr === (stmt.exp.rtype as TypeSignature).tkeystr) {
                this.pushStatement(new IRVariableInitializationDirectInvokeWithImplicitStatement(this.generateTempVarName(), this.processLocalVariableName(stmt.name), irvtype, irval, stmt.vkind === "let"));
            }
            else {
                const iiexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(irval, stmt.exp.rtype as TypeSignature), stmt.exp.rtype as TypeSignature, stmt.actualtype as TypeSignature);
                this.pushStatement(new IRVariableInitializationStatement(this.processLocalVariableName(stmt.name), irvtype, iiexp, stmt.vkind === "let"));
            }
        }
        else if(irval instanceof IRConstructExpression) {
            if(irvtype.tkeystr === (stmt.exp.rtype as TypeSignature).tkeystr) {
                this.pushStatement(new IRVariableInitializationDirectConstructorStatement(this.processLocalVariableName(stmt.name), irvtype, irval, stmt.vkind === "let"));
            }
            else {
                this.pushStatement(new IRVariableInitializationDirectConstructorWithBoxStatement(this.processLocalVariableName(stmt.name), irvtype, this.processTypeSignature(stmt.exp.rtype as TypeSignature) , irval, stmt.vkind === "let"));
            }
        }
        else {
            assert(false, "ASMToIRConverter not implemented: VariableInitializationStatement case not implemented");
        }
    }

    private flattenVariableMultiInitializationStatement(stmt: VariableMultiInitializationStatement) {
       assert(false, "Not Implemented -- flattenVariableMultiInitializationStatement");
    }

    private flattenVariableAssignmentStatement(stmt: VariableAssignmentStatement) {
        const irval = this.flattenExpressionRHS(stmt.exp);

        if(stmt.name === "_") {
            ; //just drop the expression value
        }
        else {
            const irvtype = this.processTypeSignature(stmt.vtype as TypeSignature);

            if(irval instanceof IRSimpleExpression) {
                const iconv = this.makeCoercionExplicitAsNeeded(irval, stmt.exp.rtype as TypeSignature, stmt.vtype as TypeSignature, );
                this.pushStatement(new IRVariableAssignmentStatement(this.processLocalVariableName(stmt.name), irvtype, iconv));
            }
            else if(irval instanceof IRInvokeDirectExpression) {
                if(irvtype.tkeystr === (stmt.exp.rtype as TypeSignature).tkeystr) {
                    this.pushStatement(new IRVariableAssignmentDirectInvokeStatement(this.generateTempVarName(), this.processLocalVariableName(stmt.name), irvtype, irval));    
                }
                else {
                    const iiexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(irval, stmt.exp.rtype as TypeSignature), stmt.exp.rtype as TypeSignature, stmt.vtype as TypeSignature);
                    this.pushStatement(new IRVariableAssignmentStatement(this.processLocalVariableName(stmt.name), irvtype, iiexp));
                }
            }
            else if(irval instanceof IRInvokeImplicitsExpression) {
                if(irvtype.tkeystr === (stmt.exp.rtype as TypeSignature).tkeystr) {
                    this.pushStatement(new IRVariableAssignmentDirectInvokeWithImplicitStatement(this.generateTempVarName(), this.processLocalVariableName(stmt.name), irvtype, irval));
                }
                else {
                    const iiexp = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(irval, stmt.exp.rtype as TypeSignature), stmt.exp.rtype as TypeSignature, stmt.vtype as TypeSignature);
                    this.pushStatement(new IRVariableAssignmentStatement(this.processLocalVariableName(stmt.name), irvtype, iiexp));
                }
            }
            else if(irval instanceof IRConstructExpression) {
                if(irvtype.tkeystr === (stmt.exp.rtype as TypeSignature).tkeystr) {
                    this.pushStatement(new IRVariableAssignmentDirectConstructorStatement(this.processLocalVariableName(stmt.name), irvtype, irval));
                }
                else {
                    this.pushStatement(new IRVariableAssignmentDirectConstructorWithBoxStatement(this.processLocalVariableName(stmt.name), irvtype, this.processTypeSignature(stmt.exp.rtype as TypeSignature), irval));
                }
            }
            else {
                assert(false, "ASMToIRConverter not implemented: VariableAssignmentStatement case not implemented");
            }
        }
    }

    private flattenVariableMultiAssignmentStatement(stmt: VariableMultiAssignmentStatement) {
        assert(false, "Not Implemented -- flattenVariableMultiAssignmentStatement");
    }

    private flattenReturnVoidStatement(stmt: ReturnVoidStatement) {
        if(this.currentPostconditions !== undefined) {
            assert(false, "Not Implemented -- emit postcondition check asserts");
        }

        if(this.currentImplicitReturnVar === undefined) {
            this.pushStatement(new IRReturnVoidSimpleStatement());
        }
        else {
            this.pushStatement(new IRReturnVoidWithImplicitStatement(this.currentImplicitReturnVar));
        }
    }

    private flattenReturnSingleStatement(stmt: ReturnSingleStatement) {
        let irval = this.flattenExpressionRHS(stmt.value);

        if(this.currentPostconditions !== undefined) {
            //introduce new temp variable and update irval to use it if needed (e.g. irval is not a simple expression)
            //then run all the postcondition checks

            assert(false, "Not Implemented -- emit postcondition check asserts");
        }

        if(this.currentImplicitReturnVar === undefined) {
            if(irval instanceof IRSimpleExpression) {
                const frval = this.makeCoercionExplicitAsNeeded(irval, stmt.value.rtype as TypeSignature, this.currentReturnType as TypeSignature);
                this.pushStatement(new IRReturnValueSimpleStatement(frval));
            }
            else if(irval instanceof IRInvokeDirectExpression) {
                if((stmt.value.rtype as TypeSignature).tkeystr === (this.currentReturnType as TypeSignature).tkeystr) {
                    this.pushStatement(new IRReturnDirectInvokeStatement(irval));
                }
                else {
                    const sexp = this.makeExpressionSimple(irval, stmt.value.rtype as TypeSignature);
                    const frval = this.makeCoercionExplicitAsNeeded(sexp, stmt.value.rtype as TypeSignature, this.currentReturnType as TypeSignature);

                    this.pushStatement(new IRReturnValueSimpleStatement(frval));
                }
            }
            else if(irval instanceof IRInvokeImplicitsExpression) {
                const sexp = this.makeExpressionSimple(irval, stmt.value.rtype as TypeSignature);
                const frval = this.makeCoercionExplicitAsNeeded(sexp, stmt.value.rtype as TypeSignature, this.currentReturnType as TypeSignature);

                this.pushStatement(new IRReturnValueSimpleStatement(frval));
            }
            else if(irval instanceof IRConstructExpression) {
                if((stmt.value.rtype as TypeSignature).tkeystr === (this.currentReturnType as TypeSignature).tkeystr) {
                    this.pushStatement(new IRReturnDirectConstructStatement(irval));
                }
                else {
                    this.pushStatement(new IRReturnDirectConstructWithBoxStatement(irval, this.processTypeSignature(stmt.value.rtype as TypeSignature), this.processTypeSignature(this.currentReturnType as TypeSignature)));
                }
            }
            else {
                assert(false, "ASMToIRConverter not implemented: unknown ReturnSingleStatement variant");
            }
        }
        else {
            if(irval instanceof IRSimpleExpression) {
                const frval = this.makeCoercionExplicitAsNeeded(irval, stmt.value.rtype as TypeSignature, this.currentReturnType as TypeSignature);
                this.pushStatement(new IRReturnValueImplicitStatement(frval, this.currentImplicitReturnVar));
            }
            else if(irval instanceof IRInvokeDirectExpression) {
                if((stmt.value.rtype as TypeSignature).tkeystr === (this.currentReturnType as TypeSignature).tkeystr) {
                    this.pushStatement(new IRReturnDirectInvokeImplicitStatement(irval, this.currentImplicitReturnVar));
                }
                else {
                    const sexp = this.makeExpressionSimple(irval, stmt.value.rtype as TypeSignature);
                    const frval = this.makeCoercionExplicitAsNeeded(sexp, stmt.value.rtype as TypeSignature, this.currentReturnType as TypeSignature);

                    this.pushStatement(new IRReturnValueImplicitStatement(frval, this.currentImplicitReturnVar));
                }
            }
            else if(irval instanceof IRInvokeImplicitsExpression) {
                if(((stmt.value.rtype as TypeSignature).tkeystr === (this.currentReturnType as TypeSignature).tkeystr) && (irval.ivar === this.currentImplicitReturnVar)) {
                    this.pushStatement(new IRReturnDirectInvokeImplicitPassThroughStatement(irval, this.currentImplicitReturnVar));
                }
                else {
                    const sexp = this.makeExpressionSimple(irval, stmt.value.rtype as TypeSignature);
                    const frval = this.makeCoercionExplicitAsNeeded(sexp, stmt.value.rtype as TypeSignature, this.currentReturnType as TypeSignature);

                    this.pushStatement(new IRReturnValueImplicitStatement(frval, this.currentImplicitReturnVar));
                }
            }
            else if(irval instanceof IRConstructExpression) {
                if((stmt.value.rtype as TypeSignature).tkeystr === (this.currentReturnType as TypeSignature).tkeystr) {
                    this.pushStatement(new IRReturnDirectConstructImplicitStatement(irval, this.currentImplicitReturnVar));
                }
                else {
                    this.pushStatement(new IRReturnDirectConstructWithBoxImplicitStatement(irval, this.processTypeSignature(stmt.value.rtype as TypeSignature), this.processTypeSignature(this.currentReturnType as TypeSignature), this.currentImplicitReturnVar));
                }
            }
            else {
                assert(false, "ASMToIRConverter not implemented: unknown ReturnSingleStatement with refs variant");
            }
        }
    }

    private flattenReturnMultiStatement(stmt: ReturnMultiStatement) {
        assert(false, "Not Implemented -- flattenReturnMultiStatement");
    }

    private flattenIfStatement(stmt: IfStatement): boolean {
        const [texp, ginfos] = this.flattenITestGuardSet(stmt.sinfo, stmt.cond);
        assert(ginfos.length === stmt.bbinds.length, "Internal error: binder info length mismatch");

        if(stmt.bbinds.length === 0) {
            if(ASMToIRConverter.isLiteralFalseExpression(texp)) {
                return false;
            }
            else {
                if(ASMToIRConverter.isLiteralTrueExpression(texp)) {
                    return this.flattenBlockStatement(stmt.trueBlock) || stmt.trueBlock.isterminal;
                }
                else {
                    this.pushStatementBlock();
                    this.flattenBlockStatement(stmt.trueBlock);
                    const tblock = this.popStatementBlock();

                    this.pushStatement(new IRSimpleIfStatement(texp, new IRBlockStatement(tblock)));
                    return false;
                }
            }
        }
        else {
            assert(false, "Not implemented -- IfStatement with binders");
        }
    }

    private flattenIfElseStatement(stmt: IfElseStatement): boolean {
        const [texp, ginfos] = this.flattenITestGuardSet(stmt.sinfo, stmt.cond);
        assert(ginfos.length === stmt.bbinds.length, "Internal error: binder info length mismatch");

        if(stmt.bbinds.length === 0) {
            if(ASMToIRConverter.isLiteralFalseExpression(texp)) {
                return this.flattenBlockStatement(stmt.falseBlock) || stmt.falseBlock.isterminal;
            }
            else if(ASMToIRConverter.isLiteralTrueExpression(texp)) {
                return this.flattenBlockStatement(stmt.trueBlock) || stmt.trueBlock.isterminal;
            }
            else {
                this.pushStatementBlock();
                this.flattenBlockStatement(stmt.trueBlock);
                const tblock = this.popStatementBlock();

                this.pushStatementBlock();
                this.flattenBlockStatement(stmt.falseBlock);
                const fblock = this.popStatementBlock();

                this.pushStatement(new IRSimpleIfElseStatement(texp, new IRBlockStatement(tblock), new IRBlockStatement(fblock)));
                return false;
            }
        }
        else {
            assert(false, "Not implemented -- IfElseStatement with binders");
        }
    }

    private flattenIfElifElseStatement(stmt: IfElifElseStatement): boolean {
        assert(false, "Not Implemented -- flattenIfElifElseStatement");
    }

    private flattenSwitchStatement(stmt: SwitchStatement): boolean {
        assert(false, "Not Implemented -- flattenSwitchStatement");
    }

    private flattenMatchStatement(stmt: MatchStatement): boolean {
        assert(false, "Not Implemented -- flattenMatchStatement");
    }

    private flattenDispatchPatternStatement(stmt: DispatchPatternStatement): boolean {
        assert(false, "Not Implemented -- flattenDispatchPatternStatement");
    }

    private flattenDispatchTaskStatement(stmt: DispatchTaskStatement): boolean {
        assert(false, "Not Implemented -- flattenDispatchTaskStatement");
    }

    private flattenAbortStatement(stmt: AbortStatement) {
        this.pushStatement(new IRAbortStatement(this.currentFile as string, this.convertSourceInfo(stmt.sinfo), undefined, this.registerError(this.currentFile as string, this.convertSourceInfo(stmt.sinfo), "userspec")));
    }

    private flattenAssertStatement(stmt: AssertStatement) {
        const ircond = this.flattenChkLogicExpression(stmt.cond);
        if(ASMToIRConverter.isLiteralTrueExpression(ircond)) {
            ;//no-op
        }
        else {
            this.pushStatement(new IRAssertStatement(this.currentFile as string, this.convertSourceInfo(stmt.sinfo), stmt.tag, this.registerError(this.currentFile as string, this.convertSourceInfo(stmt.sinfo), "userspec"), ircond));
        }
    }
    
    private flattenValidateStatement(stmt: ValidateStatement) {
        const ircond = this.flattenChkLogicExpression(stmt.cond);
        if(ASMToIRConverter.isLiteralTrueExpression(ircond)) {
            ;//no-op
        }
        else {
            this.pushStatement(new IRValidateStatement(this.currentFile as string, this.convertSourceInfo(stmt.sinfo), stmt.tag, this.registerError(this.currentFile as string, this.convertSourceInfo(stmt.sinfo), "userspec"), ircond));
        }
    }

    private flattenDebugStatement(stmt: DebugStatement) {
        const irval = this.makeExpressionSimple(this.flattenExpression(stmt.value), this.tproc(stmt.value.getType()));
        const irtype = this.processTypeSignature(stmt.value.getType());

        this.pushStatement(new IRDebugStatement(irtype, irval, this.currentFile as string, this.convertSourceInfo(stmt.sinfo)));
    }

    private flattenVoidRefCallStatement(stmt: VoidRefCallStatement) {
        if(stmt.exp instanceof CallNamespaceFunctionExpression) {
            const iiv = this.flattenExpression(stmt.exp);
            this.pushStatement(new IRVoidInvokeStatement(this.generateTempVarName(), iiv as IRInvokeImplicitsExpression));
        }
        else {
            assert(false, "Not Implemented -- flattenVoidRefCallStatement for other calls");
        }
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

    private flattenBlockStatement(stmt: BlockStatement): boolean {
        for(let i = 0; i < stmt.statements.length; ++i) {
            const earlyterm = this.flattenStatement(stmt.statements[i]);
            if(earlyterm) {
                return true;
            }
        }

        return false;
    }

    private flattenStatement(stmt: Statement): boolean {
        let terminal = false;

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
                terminal = this.flattenIfStatement(stmt as IfStatement);
                break;
            }
            case StatementTag.IfElseStatement: {
                terminal = this.flattenIfElseStatement(stmt as IfElseStatement);
                break;
            }
            case StatementTag.IfElifElseStatement: {
                terminal = this.flattenIfElifElseStatement(stmt as IfElifElseStatement);
                break;
            }
            case StatementTag.SwitchStatement: {
                terminal = this.flattenSwitchStatement(stmt as SwitchStatement);
                break;
            }
            case StatementTag.MatchStatement: {
                terminal = this.flattenMatchStatement(stmt as MatchStatement);
                break;
            }
            case StatementTag.DispatchPatternStatement: {
                terminal = this.flattenDispatchPatternStatement(stmt as DispatchPatternStatement);
                break;
            }
            case StatementTag.DispatchTaskStatement: {
                terminal = this.flattenDispatchTaskStatement(stmt as DispatchTaskStatement);
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

        return terminal;
    }

    private processBody(body: BodyImplementation): IRBody {
        if(body instanceof BuiltinBodyImplementation) {
            return new IRBuiltinBody(body.builtin);
        }
        else if(body instanceof HoleBodyImplementation) {
            assert(body.samplesfile === undefined, "HoleBodyImplementation with expression not supported in IR yet");
            return new IRHoleBody(body.hname, body.doccomment, undefined);
        }
        else {
            if(body instanceof ExpressionBodyImplementation) {
                this.pushStatementBlock();
                const eexp = this.flattenExpression(body.exp);

                if(eexp instanceof IRSimpleExpression) {
                    const frval = this.makeCoercionExplicitAsNeeded(eexp, this.tproc(body.exp.getType()), this.currentReturnType as TypeSignature);
                    this.pushStatement(new IRReturnValueSimpleStatement(frval));
                }
                else if(eexp instanceof IRConstructExpression) {
                    assert(false, "Not implemented -- flattenExpressionBody with construct expression body");
                }
                else {
                    if(eexp instanceof IRInvokeDirectExpression && this.tproc(body.exp.getType()).tkeystr === (this.currentReturnType as TypeSignature).tkeystr) {
                        this.pushStatement(new IRReturnDirectInvokeStatement(eexp));
                    }
                    else {
                        const sexp = this.makeExpressionSimple(eexp, this.tproc(body.exp.getType()));
                        const frval = this.makeCoercionExplicitAsNeeded(sexp, this.tproc(body.exp.getType()), this.currentReturnType as TypeSignature);

                        this.pushStatement(new IRReturnValueSimpleStatement(frval));
                    }
                }

                const stmts = this.popStatementBlock();
                return new IRStandardBody(stmts);
            }
            else {
                assert(body instanceof StandardBodyImplementation);
            
                this.pushStatementBlock();
                for(let i = 0; i < body.statements.length; ++i) {
                    const earlyterm = this.flattenStatement(body.statements[i]);
                    if(earlyterm) {
                        break;
                    }
                }
                const stmts = this.popStatementBlock();

                return new IRStandardBody(stmts);
            }
        }
    }

    private generateRequiresClauseDecl(req: PreConditionDecl): IRPreConditionDecl {
        assert(false, "Not Implemented -- generateRequiresClauseExplicitInvoke");
    }

    private generateEnsuresClauseDecl(req: PostConditionDecl): IRPostConditionDecl {
        assert(false, "Not Implemented -- generateEnsuresClauseExplicitInvoke");
    }

    private generateMemberFieldDecl(containingtype: NominalTypeSignature, mdecl: MemberFieldDecl): IRMemberFieldDecl {
        const doc = mdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        let defaultinfo: { stmts: IRStatement[], value: IRSimpleExpression } | undefined = undefined;
        if(mdecl.defaultValue !== undefined) {
            const crexp = this.assembly.tryReduceConstantExpression(mdecl.defaultValue);

            if(crexp === undefined) {
                assert(false, "ASMToIRConverter not implemented: MemberFieldDecl default value is a constant evaluatable expression");
            }
        }

        const fkey = `${containingtype.tkeystr}--${mdecl.name}`;
        return new IRMemberFieldDecl(fkey, this.processTypeSignature(containingtype), mdecl.name, this.processTypeSignature(mdecl.declaredType), defaultinfo, docstring, this.processMetaDataTags(mdecl.attributes));
    }

    private generateInvariantClauseDecl(containingtype: NominalTypeSignature, req: InvariantDecl): IRInvariantDecl {
        const encltype = this.processTypeSignature(containingtype);
        
        this.pushStatementBlock();
        const eexp = this.flattenChkLogicExpression(req.exp);
        const stmts = this.popStatementBlock();

        return new IRInvariantDecl(req.file, this.convertSourceInfo(req.sinfo), req.diagnosticTag, encltype.tkeystr, req.ii, stmts, eexp);
    }

    private generateValidateClauseDecl(containingtype: NominalTypeSignature, req: ValidateDecl): IRValidateDecl {
        const encltype = this.processTypeSignature(containingtype);
        
        this.pushStatementBlock();
        const eexp = this.flattenChkLogicExpression(req.exp);
        const stmts = this.popStatementBlock();

        return new IRValidateDecl(req.file, this.convertSourceInfo(req.sinfo), req.diagnosticTag, encltype.tkeystr, req.ii, stmts, eexp);
    }

    private processRecursiveInfo(recursive: RecursiveAnnotation): "recursive" | "recursive?" | undefined {
        if(recursive === "yes") {
            return "recursive";
        }
        else if(recursive === "cond") {
            return "recursive?";
        }
        else {
            return undefined;
        }
    }

    private processMetaDataTags(tags: DeclarationAttibute[]): IRDeclarationMetaTag[] {
        return tags.filter((a) => a.name !== "doc").map<IRDeclarationMetaTag>((mtag) => {
            const tags = mtag.tags.map((tt) => {
                return { enumType: this.processTypeSignature(tt.enumType), tag: tt.tag };
            });

            return new IRDeclarationMetaTag(mtag.name, tags);
        });
    }

    private processAssociationInfo(association: TestAssociation[]): IRTestAssociation[] {
        assert(false, "Not Implemented -- processAssociationInfo");
    }

    private processInvokeParams(params: InvokeParameterDecl[]): IRInvokeParameterDecl[] {
        return params.map<IRInvokeParameterDecl>((p) => {
            let defaultValue: { stmts: IRStatement[], value: IRSimpleExpression } | undefined = undefined;
            if(p.optDefaultValue !== undefined) {
                const crexp = this.assembly.tryReduceConstantExpression(p.optDefaultValue);
                if(crexp === undefined) {
                    assert(false, "Not Implemented -- processInvokeParams default value");
                }
            }

            if(!(p.type instanceof LambdaInvokeExpression)) {
                return new IRInvokeParameterDecl(p.name, this.processTypeSignature(p.type), p.pkind, defaultValue);

            }
            else {
                const ll = (this.currentInvokeInstantation as InvokeInstantiationInfo).lambdas.find((li) => li.pname === p.name) as { pname: string, psigkey: string, invtrgt: string };
                const tlambda = new IRLambdaParameterPackTypeSignature(ll.psigkey);
                
                return new IRInvokeParameterDecl(p.name, tlambda, p.pkind, defaultValue);
            }
        });
    }

    private generateNamespaceFunctionDecl(fdecl: NamespaceFunctionDecl, irasm: IRAssembly) {
        const ikey = (this.currentInvokeInstantation as InvokeInstantiationInfo).newikey;
        const recursive = this.processRecursiveInfo(fdecl.recursive);
        
        const params = this.processInvokeParams(fdecl.params);
        const preconds = fdecl.preconditions.map<IRPreConditionDecl>((pc) => this.generateRequiresClauseDecl(pc));
        const postconds = fdecl.postconditions.map<IRPostConditionDecl>((ec) => this.generateEnsuresClauseDecl(ec));

        const doc = fdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        if(fdecl.fkind === "predicate") {
            irasm.predicates.push(new IRPredicateDecl(ikey, recursive, params, this.processTypeSignature(fdecl.resultType), preconds, postconds, docstring, fdecl.file, this.convertSourceInfo(fdecl.sinfo)));
        }
        else {
            const body = this.processBody(fdecl.body);
            const association = (fdecl.tassoc !== undefined) ? this.processAssociationInfo(fdecl.tassoc) : undefined;

            if(fdecl.fkind === "function") {
                irasm.invokes.push(new IRInvokeDecl(ikey, recursive, params, this.processTypeSignature(fdecl.resultType), preconds, postconds, docstring, fdecl.file, this.convertSourceInfo(fdecl.sinfo), body));
            }
            else if(fdecl.fkind === "chktest" || fdecl.fkind === "errtest") {
                irasm.tests.push(new IRTestDecl(ikey, recursive, params, this.processTypeSignature(fdecl.resultType), preconds, postconds, docstring, fdecl.file, this.convertSourceInfo(fdecl.sinfo), fdecl.fkind as "chktest" | "errtest", association, body));
            }
            else {
                irasm.examples.push(new IRExampleDecl(ikey, recursive, params, this.processTypeSignature(fdecl.resultType), preconds, postconds, docstring, fdecl.file, this.convertSourceInfo(fdecl.sinfo), association, body));
            }
        }
    }

/*
    private generateTypeFunctionDecl(fdecl: TypeFunctionDecl, invks: IRInvokeDecl[], preds: IRPredicateDecl[]) {
        assert(false, "Not Implemented -- generateTypeFunctionDecl");
    }

    private generateMethodDecl(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecl: MethodDecl, invks: IRInvokeDecl[]) {
        assert(false, "Not Implemented -- generateMethodDecl");
    }

    private generateTaskMethodDecl(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecl: TaskMethodDecl, invks: IRInvokeDecl[]) {
        assert(false, "Not implemented -- generateTaskMethodDecl");
    }

    private generateTaskActionDecl(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecl: TaskActionDecl, adecls: IRTaskActionDecl[]) {
        assert(false, "Not implemented -- generateTaskActionDecl");
    }

    private generateConstMemberDecl(tdecl: AbstractNominalTypeDecl, cdecl: ConstMemberDecl, typeinst: TypeInstantiationInfo | undefined): IRConstantDecl {
        this.initCodeProcessingContext(tdecl.file, false, cdecl.declaredType, undefined, undefined, typeinst, undefined);

        this.pushStatementBlock();
        const irval = this.flattenExpression(cdecl.value);
        
        const doc = cdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;
        
        const stmts = this.popStatementBlock();
        const expr = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(irval, cdecl.value.getType()), cdecl.value.getType(), cdecl.declaredType);

        return new IRConstantDecl(cdecl.name, this.processTypeSignature(cdecl.declaredType), stmts, expr, docstring);
    }
*/
    private generateEnumTypeDecl(tdecl: EnumTypeDecl, tinst: TypeInstantiationInfo): IREnumTypeDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        return new IREnumTypeDecl(tinst.tkey, docstring, tdecl.file, this.convertSourceInfo(tdecl.sinfo), [...tdecl.members]);
    }

    private generateTypedeclTypeDecl(tdecl: TypedeclTypeDecl, tinst: TypeInstantiationInfo): IRTypedeclTypeDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        const invariants = tdecl.invariants.map<IRInvariantDecl>((inv) => this.generateInvariantClauseDecl(tinst.tsig as NominalTypeSignature, inv));
        const validates = tdecl.validates.map<IRValidateDecl>((val) => this.generateValidateClauseDecl(tinst.tsig as NominalTypeSignature, val));

        const saturatedProvides = tdecl.saturatedProvides.map((sp => this.processTypeSignature(sp)));

        const allInvariants = tdecl.allInvariants.map((inv, jj) => {
            return { containingtype: this.processTypeSignature(inv.containingtype), ii: jj };
        });
        const allValidates = tdecl.allValidates.map((val, jj) => {
            return { containingtype: this.processTypeSignature(val.containingtype), ii: jj };
        });

        return new IRTypedeclTypeDecl(tinst.tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstring, this.processMetaDataTags(tdecl.attributes), tdecl.file, this.convertSourceInfo(tdecl.sinfo), this.processTypeSignature(tdecl.valuetype as TypeSignature), (tdecl.valuetype as NominalTypeSignature).decl.isKeyTypeRestricted(), (tdecl.valuetype as NominalTypeSignature).decl.isNumericRestricted());
    }

    private generateTypedeclCStringDecl(tdecl: TypedeclTypeDecl, tinst: TypeInstantiationInfo): IRTypedeclCStringDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        const invariants = tdecl.invariants.map<IRInvariantDecl>((inv) => this.generateInvariantClauseDecl(tinst.tsig as NominalTypeSignature, inv));
        const validates = tdecl.validates.map<IRValidateDecl>((val) => this.generateValidateClauseDecl(tinst.tsig as NominalTypeSignature, val));

        const saturatedProvides = tdecl.saturatedProvides.map((sp => this.processTypeSignature(sp)));

        const allInvariants = tdecl.allInvariants.map((inv, jj) => {
            return { containingtype: this.processTypeSignature(inv.containingtype), ii: jj };
        });
        const allValidates = tdecl.allValidates.map((val, jj) => {
            return { containingtype: this.processTypeSignature(val.containingtype), ii: jj };
        });

        let rngchk: {min: string | undefined, max: string | undefined} | undefined = undefined;
        if(tdecl.optsizerng !== undefined) {
            rngchk = {min: tdecl.optsizerng.min, max: tdecl.optsizerng.max};
        }
        const rechk = tdecl.optofexp !== undefined ? this.flattenExpression(tdecl.optofexp) as IRLiteralCRegexExpression : undefined;

        return new IRTypedeclCStringDecl(tinst.tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstring, this.processMetaDataTags(tdecl.attributes), tdecl.file, this.convertSourceInfo(tdecl.sinfo), rngchk, rechk);
    }

    private generateTypedeclStringDecl(tdecl: TypedeclTypeDecl, tinst: TypeInstantiationInfo): IRTypedeclStringDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        const invariants = tdecl.invariants.map<IRInvariantDecl>((inv) => this.generateInvariantClauseDecl(tinst.tsig as NominalTypeSignature, inv));
        const validates = tdecl.validates.map<IRValidateDecl>((val) => this.generateValidateClauseDecl(tinst.tsig as NominalTypeSignature, val));

        const saturatedProvides = tdecl.saturatedProvides.map((sp => this.processTypeSignature(sp)));

        const allInvariants = tdecl.allInvariants.map((inv, jj) => {
            return { containingtype: this.processTypeSignature(inv.containingtype), ii: jj };
        });
        const allValidates = tdecl.allValidates.map((val, jj) => {
            return { containingtype: this.processTypeSignature(val.containingtype), ii: jj };
        });

        let rngchk: {min: string | undefined, max: string | undefined} | undefined = undefined;
        if(tdecl.optsizerng !== undefined) {
            rngchk = {min: tdecl.optsizerng.min, max: tdecl.optsizerng.max};
        }
        const rechk = tdecl.optofexp !== undefined ? this.flattenExpression(tdecl.optofexp) as IRLiteralUnicodeRegexExpression : undefined;

        return new IRTypedeclStringDecl(tinst.tkey, invariants, validates, saturatedProvides, allInvariants, allValidates, docstring, this.processMetaDataTags(tdecl.attributes), tdecl.file, this.convertSourceInfo(tdecl.sinfo), rngchk, rechk);
    }

    private generatePrimitiveEntityTypeDecl(tdecl: PrimitiveEntityTypeDecl, tinst: TypeInstantiationInfo): IRPrimitiveEntityTypeDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        return new IRPrimitiveEntityTypeDecl(tdecl.name, docstring, tdecl.file, this.convertSourceInfo(tdecl.sinfo));
    }

    private generateOkTypeDecl(tdecl: OkTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IROkTypeDecl {
        assert(false, "Not Implemented -- generateOkTypeDecl");
    }

    private generateFailTypeDecl(tdecl: FailTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRFailTypeDecl {
        assert(false, "Not Implemented -- generateFailTypeDecl");
    }

    private generateAPIErrorTypeDecl(tdecl: APIErrorTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRAPIErrorTypeDecl {
        assert(false, "Not Implemented -- generateAPIErrorTypeDecl");
    }

    private generateAPIRejectedTypeDecl(tdecl: APIRejectedTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRAPIRejectedTypeDecl {
        assert(false, "Not Implemented -- generateAPIRejectedTypeDecl");
    }

    private generateAPIDeniedTypeDecl(tdecl: APIDeniedTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRAPIDeniedTypeDecl {
        assert(false, "Not Implemented -- generateAPIDeniedTypeDecl");
    }

    private generateAPIFlaggedTypeDecl(tdecl: APIFlaggedTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRAPIFlaggedTypeDecl {
        assert(false, "Not Implemented -- generateAPIFlaggedTypeDecl");
    }

    private generateAPISuccessTypeDecl(tdecl: APISuccessTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRAPISuccessTypeDecl {
        assert(false, "Not Implemented -- generateAPISuccessTypeDecl");
    }

    private generateSomeTypeDecl(tdecl: SomeTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRSomeTypeDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);
        
        const encloption = tdecl.saturatedProvides.map((sp) => this.processTypeSignature(sp));

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        const oftype = this.processTypeSignature((this.tproc(tinst.tsig) as NominalTypeSignature).alltermargs[0] as TypeSignature);

        return new IRSomeTypeDecl(tinst.tkey, encloption, docstring, tdecl.file, this.convertSourceInfo(tdecl.sinfo), oftype);
    }

    private generateMapEntryTypeDecl(tdecl: MapEntryTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRMapEntryTypeDecl {
        assert(false, "Not Implemented -- generateMapEntryTypeDecl");
    }

    private generateListTypeDecl(tdecl: ListTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRListTypeDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        const oftype = this.processTypeSignature((this.tproc(tinst.tsig) as NominalTypeSignature).alltermargs[0] as TypeSignature);

        return new IRListTypeDecl(tinst.tkey, docstring, tdecl.file, this.convertSourceInfo(tdecl.sinfo), oftype);
    }

    private generateStackTypeDecl(tdecl: StackTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRStackTypeDecl {
        assert(false, "Not Implemented -- generateStackTypeDecl");
    }

    private generateQueueTypeDecl(tdecl: QueueTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRQueueTypeDecl {
        assert(false, "Not Implemented -- generateQueueTypeDecl");
    }

    private generateSetTypeDecl(tdecl: SetTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRSetTypeDecl {
        assert(false, "Not Implemented -- generateSetTypeDecl");
    }

    private generateMapTypeDecl(tdecl: MapTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRMapTypeDecl {
        assert(false, "Not Implemented -- generateMapTypeDecl");
    }

    private generateEventListTypeDecl(tdecl: EventListTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IREventListTypeDecl {
        assert(false, "Not Implemented -- generateEventListTypeDecl");
    }

    private generateEntityTypeDecl(tdecl: EntityTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IREntityTypeDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        let etag: "std" | "status" | "event" = "std";
        if(tdecl.etag === AdditionalTypeDeclTag.Status) {
            etag = "status";
        }
        if(tdecl.etag === AdditionalTypeDeclTag.Event) {
            etag = "event";
        }

        const bfinfo = tdecl.saturatedBFieldInfo.map((bf) => {
            const bfirt = this.processTypeSignature(bf.containingtype);
            const fkey = `${bfirt.tkeystr}--${bf.name}`;
            return { containingtype: bfirt, fkey: fkey, fname: bf.name, ftype: this.processTypeSignature(bf.type) };
        });

        const allInvariants = tdecl.allInvariants.map((vv) => {
            return { containingtype: this.processTypeSignature(vv.containingtype), ii: vv.ii };
        });
        const allValidates = tdecl.allValidates.map((vv) => {
            return { containingtype: this.processTypeSignature(vv.containingtype), ii: vv.ii };
        });

        return new IREntityTypeDecl(tinst.tkey, 
            tdecl.invariants.map<IRInvariantDecl>((inv) => this.generateInvariantClauseDecl(tinst.tsig as NominalTypeSignature, inv)),
            tdecl.validates.map<IRValidateDecl>((val) => this.generateValidateClauseDecl(tinst.tsig as NominalTypeSignature, val)),
            tdecl.fields.map<IRMemberFieldDecl>((f) => this.generateMemberFieldDecl(tinst.tsig as NominalTypeSignature, f)),
            etag,
            tdecl.saturatedProvides.map((sp) => this.processTypeSignature(sp)),
            bfinfo,
            allInvariants,
            allValidates,
            docstring,
            this.processMetaDataTags(tdecl.attributes),
            tdecl.file,
            this.convertSourceInfo(tdecl.sinfo)
        );
    }

    private generateOptionTypeDecl(tdecl: OptionTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IROptionTypeDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        const oftype = this.processTypeSignature((this.tproc(tinst.tsig) as NominalTypeSignature).alltermargs[0] as TypeSignature);
        
        const somedecl = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Some") as SomeTypeDecl;
        const sometype = this.processTypeSignature(new NominalTypeSignature(tinst.tsig.sinfo, undefined, somedecl, [(this.tproc(tinst.tsig) as NominalTypeSignature).alltermargs[0] as TypeSignature]));
        
        return new IROptionTypeDecl(tinst.tkey, docstring, tdecl.file, this.convertSourceInfo(tdecl.sinfo), oftype, sometype);
    }

    private generateResultTypeDecl(tdecl: ResultTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRResultTypeDecl {
        assert(false, "Not Implemented -- generateResultTypeDecl");
    }

    private generateAPIResultTypeDecl(tdecl: APIResultTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRAPIResultTypeDecl {
        assert(false, "Not Implemented -- generateAPIResultTypeDecl");
    }

    private generateConceptTypeDecl(tdecl: ConceptTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRConceptTypeDecl {
        this.initCodeProcessingContext(tdecl.file, false, tinst.tsig, undefined, undefined, tinst, undefined);

        const doc = tdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;

        const bfinfo = tdecl.saturatedBFieldInfo.map((bf) => {
            const fkey = `${(tinst.tsig as NominalTypeSignature).tkeystr}--${bf.name}`;
            return { containingtype: this.processTypeSignature(bf.containingtype), fkey: fkey, fname: bf.name, ftype: this.processTypeSignature(bf.type) };
        });

        return new IRConceptTypeDecl(tinst.tkey, 
            tdecl.invariants.map<IRInvariantDecl>((inv) => this.generateInvariantClauseDecl(tinst.tsig as NominalTypeSignature, inv)),
            tdecl.validates.map<IRValidateDecl>((val) => this.generateValidateClauseDecl(tinst.tsig as NominalTypeSignature, val)),
            tdecl.fields.map<IRMemberFieldDecl>((f) => this.generateMemberFieldDecl(tinst.tsig as NominalTypeSignature, f)),
            tdecl.saturatedProvides.map((sp) => this.processTypeSignature(sp)),
            bfinfo,
            docstring,
            this.processMetaDataTags(tdecl.attributes),
            tdecl.file,
            this.convertSourceInfo(tdecl.sinfo)
        );
    }

    private generateDatatypeMemberEntityTypeDecl(tdecl: DatatypeMemberEntityTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRDatatypeMemberEntityTypeDecl {
        assert(false, "Not Implemented -- generateDatatypeMemberEntityTypeDecl");
    }

    private generateDatatypeTypeDecl(tdecl: DatatypeTypeDecl, tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRDatatypeTypeDecl {
        assert(false, "Not Implemented -- generateDatatypeTypeDecl");
    }

    private generateAPIDecl(adecl: APIDecl, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRAPIDecl {
        assert(false, "Not implemented -- checkAPIDecl");
    }

    private generateAgentDecl(adecl: AgentDecl, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRAgentDecl {
        assert(false, "Not implemented -- checkAgentDecl");
    }

    private generateTaskDecl(tdecl: TaskDecl, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]): IRTaskDecl {
        assert(false, "Not implemented -- checkTaskDecl");
    }

    private generateNamespaceConstDecl(cdecl: NamespaceConstDecl): IRConstantDecl {
        this.initCodeProcessingContext(cdecl.file, false, cdecl.declaredType, undefined, undefined, undefined, undefined);

        this.pushStatementBlock();
        const irval = this.flattenExpression(cdecl.value);
        
        const doc = cdecl.attributes.find((a) => a.name === "doc");
        const docstring = (doc !== undefined) ? new IRDeclarationDocString(doc.text as string) :  undefined;
        
        const stmts = this.popStatementBlock();
        const expr = this.makeCoercionExplicitAsNeeded(this.makeExpressionSimple(irval, this.tproc(cdecl.value.getType())), this.tproc(cdecl.value.getType()), cdecl.declaredType);

        return new IRConstantDecl(cdecl.name, this.processTypeSignature(cdecl.declaredType), stmts, expr, docstring);
    }

    private generateNamespaceTypeDecl(tinst: TypeInstantiationInfo, irasm: IRAssembly, iinfo: NamespaceInstantiationInfo[]) {
        const tt = (tinst.tsig as NominalTypeSignature).decl;
        if(tt instanceof EnumTypeDecl) {
            const edecl = this.generateEnumTypeDecl(tt, tinst);
            irasm.enums.push(edecl);
            irasm.alltypes.set(edecl.tkey, edecl);
        }
        else if(tt instanceof TypedeclTypeDecl) {
            const oftype = this.processTypeSignature((tt.valuetype as TypeSignature));
            if(oftype.tkeystr === "CString") {
                const csdecl = this.generateTypedeclCStringDecl(tt, tinst)
                irasm.cstringoftypedecls.push(csdecl);
                irasm.alltypes.set(csdecl.tkey, csdecl);
            }
            else if(oftype.tkeystr === "String") {
                const sdecl = this.generateTypedeclStringDecl(tt, tinst);
                irasm.stringoftypedecls.push(sdecl);
                irasm.alltypes.set(sdecl.tkey, sdecl);
            }
            else {
                const ttdecl = this.generateTypedeclTypeDecl(tt, tinst);
                irasm.typedecls.push(ttdecl);
                irasm.alltypes.set(ttdecl.tkey, ttdecl);
            }
        }
        else if(tt instanceof PrimitiveEntityTypeDecl) {
            const pdecl = this.generatePrimitiveEntityTypeDecl(tt, tinst);
            irasm.primitives.push(pdecl);
            irasm.alltypes.set(pdecl.tkey, pdecl);
        }
        else if(tt instanceof OkTypeDecl) {
            const okdecl = this.generateOkTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(okdecl);
            irasm.alltypes.set(okdecl.tkey, okdecl);
        }
        else if(tt instanceof FailTypeDecl) {
            const faildecl = this.generateFailTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(faildecl);
            irasm.alltypes.set(faildecl.tkey, faildecl);
        }
        else if(tt instanceof APIErrorTypeDecl) {
            const errdecl = this.generateAPIErrorTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(errdecl);
            irasm.alltypes.set(errdecl.tkey, errdecl);
        }
        else if(tt instanceof APIRejectedTypeDecl) {
            const rejecteddecl = this.generateAPIRejectedTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(rejecteddecl);
            irasm.alltypes.set(rejecteddecl.tkey, rejecteddecl);
        }
        else if(tt instanceof APIDeniedTypeDecl) {
            const denieddecl = this.generateAPIDeniedTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(denieddecl);
            irasm.alltypes.set(denieddecl.tkey, denieddecl);
        }
        else if(tt instanceof APIFlaggedTypeDecl) {
            const flaggeddecl = this.generateAPIFlaggedTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(flaggeddecl);
            irasm.alltypes.set(flaggeddecl.tkey, flaggeddecl);
        }
        else if(tt instanceof APISuccessTypeDecl) {
            const successdecl = this.generateAPISuccessTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(successdecl);
            irasm.alltypes.set(successdecl.tkey, successdecl);
        }
        else if(tt instanceof SomeTypeDecl) {
            const somedecl = this.generateSomeTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(somedecl);
            irasm.alltypes.set(somedecl.tkey, somedecl);
        }
        else if(tt instanceof MapEntryTypeDecl) {
            const mapdecl = this.generateMapEntryTypeDecl(tt, tinst, irasm, iinfo);
            irasm.constructables.push(mapdecl);
            irasm.alltypes.set(mapdecl.tkey, mapdecl);
        }
        else if(tt instanceof ListTypeDecl) {
            const listdecl = this.generateListTypeDecl(tt, tinst, irasm, iinfo);
            irasm.collections.push(listdecl);
            irasm.alltypes.set(listdecl.tkey, listdecl);
        }
        else if(tt instanceof StackTypeDecl) {
            const stackdecl = this.generateStackTypeDecl(tt, tinst, irasm, iinfo);
            irasm.collections.push(stackdecl);
            irasm.alltypes.set(stackdecl.tkey, stackdecl);
        }
        else if(tt instanceof QueueTypeDecl) {
            const queuedecl = this.generateQueueTypeDecl(tt, tinst, irasm, iinfo);
            irasm.collections.push(queuedecl);
            irasm.alltypes.set(queuedecl.tkey, queuedecl);
        }
        else if(tt instanceof SetTypeDecl) {
            const setdecl = this.generateSetTypeDecl(tt, tinst, irasm, iinfo);
            irasm.collections.push(setdecl);
            irasm.alltypes.set(setdecl.tkey, setdecl);
        }
        else if(tt instanceof MapTypeDecl) {
            const mapdecl = this.generateMapTypeDecl(tt, tinst, irasm, iinfo);
            irasm.collections.push(mapdecl);
            irasm.alltypes.set(mapdecl.tkey, mapdecl);
        }
        else if(tt instanceof EventListTypeDecl) {
            const eldecl = this.generateEventListTypeDecl(tt, tinst, irasm, iinfo);
            irasm.eventlists.push(eldecl);
            irasm.alltypes.set(eldecl.tkey, eldecl);
        }
        else if(tt instanceof EntityTypeDecl) {
            const eedecl = this.generateEntityTypeDecl(tt, tinst, irasm, iinfo);
            irasm.entities.push(eedecl);
            irasm.alltypes.set(eedecl.tkey, eedecl);
        }
        else if(tt instanceof OptionTypeDecl) {
            const optdecl = this.generateOptionTypeDecl(tt, tinst, irasm, iinfo);
            irasm.pconcepts.push(optdecl);
            irasm.alltypes.set(optdecl.tkey, optdecl);
        }
        else if(tt instanceof ResultTypeDecl) {
            const resdecl = this.generateResultTypeDecl(tt, tinst, irasm, iinfo);
            irasm.pconcepts.push(resdecl);
            irasm.alltypes.set(resdecl.tkey, resdecl);
        }
        else if(tt instanceof APIResultTypeDecl) {
            const apidecl = this.generateAPIResultTypeDecl(tt, tinst, irasm, iinfo);
            irasm.pconcepts.push(apidecl);
            irasm.alltypes.set(apidecl.tkey, apidecl);
        }
        else if(tt instanceof ConceptTypeDecl) {
            const cptdecl = this.generateConceptTypeDecl(tt, tinst, irasm, iinfo);
            irasm.concepts.push(cptdecl);
            irasm.alltypes.set(cptdecl.tkey, cptdecl);
        }
        else if(tt instanceof DatatypeMemberEntityTypeDecl) {
            const dmdecl = this.generateDatatypeMemberEntityTypeDecl(tt, tinst, irasm, iinfo);
            irasm.datamembers.push(dmdecl);
            irasm.alltypes.set(dmdecl.tkey, dmdecl);
        }
        else if(tt instanceof DatatypeTypeDecl) {
            const dtdecl = this.generateDatatypeTypeDecl(tt, tinst, irasm, iinfo);
            irasm.datatypes.push(dtdecl);
            irasm.alltypes.set(dtdecl.tkey, dtdecl);
        }
        else {
            assert(false, "Unknown type decl kind");
        }
    }

    private testEmitEnabled(fdecl: NamespaceFunctionDecl): boolean {
        if(!this.generateTestInfo) {
            return false;
        }

        if(this.testfilefilter === undefined && this.testfilters === undefined) {
            return true;
        }

        let matchfile = false;
        if(this.testfilefilter !== undefined) {
            matchfile = this.testfilefilter.some((ff) => fdecl.file.endsWith(ff));
        }

        let matchfilter = false;
        if(this.testfilters !== undefined) {
            const assoc = fdecl.tassoc;

            matchfilter = assoc !== undefined && this.testfilters.some((tmatch) => assoc.some((asc) => asc.isMatchWith(tmatch)));
        }

        return matchfile || matchfilter;
    }

    private emitNamespaceDeclaration(decl: NamespaceDeclaration, asminstantiation: NamespaceInstantiationInfo, aainsts: NamespaceInstantiationInfo[], irasm: IRAssembly) {
        for(let i = 0; i < decl.subns.length; ++i) {
            const subdecl = decl.subns[i];
            const nsii = aainsts.find((ai) => ai.ns.emit() === subdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                this.emitNamespaceDeclaration(decl.subns[i], nsii, aainsts, irasm);
            }
        }

        for(let i = 0; i < decl.consts.length; ++i) {
            this.generateNamespaceConstDecl(decl.consts[i]);
        }

        for(let i = 0; i < decl.functions.length; ++i) {
            const finst = asminstantiation.functionbinds.get(decl.functions[i].resolvename as string);
            if(finst !== undefined && (decl.functions[i].fkind !== "predicate" || decl.functions[i].fkind !== "function" || this.testEmitEnabled(decl.functions[i]))) {
                for(let j = 0; j < finst.length; ++j) {
                    const fdecl = decl.functions[i];
                    const implicitreturn = fdecl.params.find((p) => p.pkind !== undefined);

                    this.initCodeProcessingContext(fdecl.file, false, fdecl.resultType, implicitreturn !== undefined ? implicitreturn.name : undefined, fdecl.postconditions.length !== 0 ? fdecl.postconditions : undefined, undefined, finst[j]);
                    this.generateNamespaceFunctionDecl(fdecl, irasm);
                }
            }
        }
        
        for(let i = 0; i < decl.typedecls.length; ++i) {
            const tinst = asminstantiation.typebinds.get(decl.typedecls[i].name);
            if(tinst !== undefined) {
                for(let j = 0; j < tinst.length; ++j) {
                    this.generateNamespaceTypeDecl(tinst[j], irasm, aainsts);
                }
            }
        }

        //apis
        for(let i = 0; i < decl.apis.length; ++i) {
            irasm.apis.push(this.generateAPIDecl(decl.apis[i], irasm, aainsts));
        }

        //agents
        for(let i = 0; i < decl.agents.length; ++i) {
            irasm.agents.push(this.generateAgentDecl(decl.agents[i], irasm, aainsts));
        }

        //tasks
        for(let i = 0; i < decl.tasks.length; ++i) {
            irasm.tasks.push(this.generateTaskDecl(decl.tasks[i], irasm, aainsts));
        }
    }

    static generateIR(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[], testfilefilter: string[] | undefined): IRAssembly {
        const emitter = new ASMToIRConverter(assembly, testfilefilter !== undefined, testfilefilter, undefined);
        const irasm = new IRAssembly();

        //emit each of the assemblies
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            const nsdecl = assembly.toplevelNamespaces[i];
            const nsii = asminstantiation.find((ai) => ai.ns.emit() === nsdecl.fullnamespace.emit());

            if(nsii !== undefined) {
                emitter.emitNamespaceDeclaration(nsdecl, nsii, asminstantiation, irasm);
            }
        }

        irasm.computeSubtypeInfo();
        irasm.computeTypeDependencyInfo();

        return irasm;
    }
}

export {
    ASMToIRConverter
};
