import assert from "node:assert";

import { JSCodeFormatter, EmitNameManager } from "./jsemitter_support.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, ArgumentValue, AssertStatement, BinAddExpression, BinderInfo, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefInvokeExpression, CallRefSelfExpression, CallRefThisExpression, CallRefVariableExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, CreateDirectExpression, DebugStatement, EmptyStatement, EnvironmentBracketStatement, EnvironmentUpdateStatement, Expression, ExpressionBodyImplementation, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, ITestFail, ITestNone, ITestOk, ITestSome, ITestType, KeyCompareEqExpression, KeyCompareLessExpression, LambdaInvokeExpression, LetExpression, LiteralExpressionValue, LiteralNoneExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PostfixProjectFromNames, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RefArgumentValue, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SafeConvertExpression, SelfUpdateStatement, SpecialConstructorExpression, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, SynthesisBodyImplementation, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskEventEmitStatement, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, UpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VarUpdateStatement, VoidRefCallStatement } from "../../frontend/body.js";
import { AbstractCollectionTypeDecl, AbstractNominalTypeDecl, APIDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, ConstMemberDecl, ConstructableTypeDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, FailTypeDecl, EventListTypeDecl, FunctionInvokeDecl, InvariantDecl, InvokeParameterDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TaskDecl, TypedeclTypeDecl, TypeFunctionDecl, ValidateDecl, AbstractEntityTypeDecl, TestAssociation } from "../../frontend/assembly.js";
import { EListTypeSignature, FullyQualifiedNamespace, NominalTypeSignature, TemplateNameMapper, TemplateTypeSignature, TypeSignature } from "../../frontend/type.js";
import { BuildLevel, CodeFormatter, isBuildLevelEnabled, SourceInfo } from "../../frontend/build_decls.js";
import { NamespaceInstantiationInfo, FunctionInstantiationInfo, MethodInstantiationInfo, TypeInstantiationInfo } from "../../frontend/instantiation_map.js";

const prefix = 
'"use strict";\n' +
'let _$consts = {};\n' +
'\n' +
'import { $VRepr, _$softfails, _$supertypes, _$fisSubtype, _$fisNotSubtype, _$fasSubtype, _$fasNotSubtype, _$None, _$not, _$negate, _$add, _$sub, _$mult, _$div, _$bval, _$fkeq, _$fkeqopt, _$fkneq, _$fkneqopt, _$fkless, _$fnumeq, _$fnumless, _$fnumlesseq, _$exhaustive, _$abort, _$assert, _$formatchk, _$invariant, _$validate, _$precond, _$softprecond, _$postcond, _$softpostcond, _$memoconstval, _$accepts } from "./runtime.mjs";\n' +
'import { _$setnone_lit, _$parsemap, _$emitmap, _$parseBSQON, _$emitBSQON } from "./bsqon.mjs";\n' +
'\n'
;

class JSEmitter {
    readonly assembly: Assembly;
    readonly asminstantiation: NamespaceInstantiationInfo[];
    readonly mode: "release" | "debug";
    readonly buildlevel: BuildLevel;

    readonly generateTestInfo: boolean;
    readonly testfilefilter: string[] | undefined;
    readonly testfilters: TestAssociation[] | undefined;

    //map from files with tests to the list of tests
    readonly testgroups: [string, string[]][] = [];

    currentfile: string | undefined;
    currentns: NamespaceDeclaration | undefined;

    mapper: TemplateNameMapper | undefined;
    optrefreturn: string | undefined = undefined;
    returncompletecall: string | undefined = undefined;

    bindernames: Set<string> = new Set();

    constructor(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[], mode: "release" | "debug", buildlevel: BuildLevel, generateTestInfo: boolean, testfilefilter: string[] | undefined, testfilters: TestAssociation[] | undefined) {
        this.assembly = assembly;
        this.asminstantiation = asminstantiation;

        this.mode = mode;
        this.buildlevel = buildlevel;

        this.generateTestInfo = generateTestInfo;
        this.testfilefilter = testfilefilter;
        this.testfilters = testfilters;

        this.currentfile = undefined;
        this.currentns = undefined;
    }

    private tproc(ttype: TypeSignature): TypeSignature {
        return this.mapper !== undefined ? ttype.remapTemplateBindings(this.getTemplateMapper()) : ttype;
    }

    private getCurrentNamespace(): NamespaceDeclaration {
        assert(this.currentns !== undefined, "Current namespace is not set");
        return this.currentns;
    }

    private getCurrentINNS(): string {
        assert(this.currentns !== undefined, "Current namespace is not set");
        return '"' + this.currentns.fullnamespace.ns.join("::") + '"';
    }

    private getErrorInfo(msg: string, sinfo: SourceInfo, diagnosticTag: string | undefined): string | undefined {
        if(this.mode === "release") {
            return diagnosticTag;
        }
        else {
            let ff: string = "[internal]";
            if(this.currentfile !== undefined) {
                const fnameidex = this.currentfile.lastIndexOf("/");
                ff = this.currentfile.slice(fnameidex + 1);
            }

            return `"${msg}${diagnosticTag !== undefined ? ("[" + diagnosticTag + "]") : ""} @ ${ff}:${sinfo.line}"`;
        }
    }

    private getTemplateMapper(): TemplateNameMapper {
        assert(this.mapper !== undefined, "Template mapper is not set");
        return this.mapper;
    }

    private emitITestAsTest_None(val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            return vtype.tkeystr === "None" ? (isnot ? "false" : "true") : (isnot ? "true" : "false");
        }
        else {
            return val + (isnot ? "._$isNotNone()" : "._$isNone()");
        }
    }

    private emitITestAsTest_Some(val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            return vtype.tkeystr.startsWith("Some") ? (isnot ? "false" : "true") : (isnot ? "true" : "false");
        }
        else {
            return val + (isnot ? "._$isNotSome()" : "._$isSome()");
        }
    }

    private emitITestAsTest_Ok(val: string, vtype: TypeSignature, isnot: boolean): string {
        const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
        const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);

        if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            return vtype.tkeystr === oktype.tkeystr ? (isnot ? "false" : "true") : (isnot ? "true" : "false");
        }
        else {
            return val + (isnot ? "._$isNot" : "._$is") + `(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oktype)})`;
        }
    }

    private emitITestAsTest_Fail(val: string, vtype: TypeSignature, isnot: boolean): string {
        const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
        const failtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getFailType(), (vtype as NominalTypeSignature).alltermargs);

        if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            return vtype.tkeystr === failtype.tkeystr ? (isnot ? "false" : "true") : (isnot ? "true" : "false");
        }
        else {
            return val + (isnot ? "._$isNot" : "._$is") + `(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), failtype)})`;
        }
    }

    private emitITestAsTest_Type(val: string, vtype: TypeSignature, oftype: TypeSignature, isnot: boolean): string {
        if(vtype instanceof EListTypeSignature) {
            if(!(oftype instanceof EListTypeSignature)) {
                return isnot ? "true" : "false";
            }
            else {
                return vtype.tkeystr === oftype.tkeystr ? (isnot ? "false" : "true") : (isnot ? "true" : "false");
            }
        }
        else if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            if(EmitNameManager.isUniqueTypeForSubtypeChecking(oftype)) {
                return vtype.tkeystr === oftype.tkeystr ? (isnot ? "false" : "true") : (isnot ? "true" : "false");
            }
            else {
                if(!EmitNameManager.isMethodCallObjectRepr(vtype)) {
                    const testop = isnot ? "_$isNotSubtype" : "_$isSubtype";
                    return `${val}.${testop}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype as NominalTypeSignature)})`; 
                }                    
                else {
                    if(EmitNameManager.isNoneType(vtype)) {
                        if(EmitNameManager.isOptionType(oftype)) {
                            return isnot ? "false" : "true";
                        }
                        else {
                            return isnot ? "true" : "false";
                        }
                    }
                    else {
                        const testop = isnot ? "_$fisNotSubtype" : "_$fisSubtype";
                        return `${testop}(${EmitNameManager.generateAccessorForTypeKey(this.currentns as NamespaceDeclaration, vtype as NominalTypeSignature)}, ${EmitNameManager.generateAccessorForTypeKey(this.currentns as NamespaceDeclaration, oftype as NominalTypeSignature)})`;
                    }
                }
            }
        }
        else {
            if(EmitNameManager.isUniqueTypeForSubtypeChecking(oftype)) {
                const testop = isnot ? "_$isNot" : "_$is";
                return `${val}.${testop}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype as NominalTypeSignature)})`;
            }
            else {
     
                if(EmitNameManager.isOptionType(oftype)) {
                    const testop = isnot ? "_$isNotOptionSubtype" : "_$isOptionSubtype";
                    return `${val}.${testop}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype as NominalTypeSignature)})`;
                }
                else {
                    const testop = isnot ? "_$isNotSubtype" : "_$isSubtype";
                    return `${val}.${testop}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype as NominalTypeSignature)})`;
                }
            }
        }
    }
    
    private processITestAsTest(val: string, vtype: TypeSignature, tt: ITest): string {
        const vvtype = this.tproc(vtype);
        
        if(tt instanceof ITestType) {
            return this.emitITestAsTest_Type(val, vvtype, this.tproc(tt.ttype), tt.isnot);
        }
        else {
            if(tt instanceof ITestNone) {
                return this.emitITestAsTest_None(val, vvtype, tt.isnot);
            }
            else if(tt instanceof ITestSome) {
                return this.emitITestAsTest_Some(val, vvtype, tt.isnot);
            }
            else if(tt instanceof ITestOk) {
                return this.emitITestAsTest_Ok(val, vvtype, tt.isnot);
            }
            else {
                assert(tt instanceof ITestFail, "missing case in ITest");
                return this.emitITestAsTest_Fail(val, vvtype, tt.isnot);
            }
        }
    }

    private emitITestAsConvert_None(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            const mfail = `_$abort(${this.getErrorInfo("Failed type convert", sinfo, undefined)})`
            return vtype.tkeystr === "None" ? (isnot ? mfail : val) : (isnot ? val : mfail);
        }
        else {
            const emsg = this.getErrorInfo(isnot ? "expected Some but got None" : "expected None but got Some", sinfo, undefined);
            return val + (isnot ? `._$asNotNone(${emsg})` : `._$asNone(${emsg})`);
        }
    }

    private emitITestAsConvert_Some(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            const mfail = `_$abort(${this.getErrorInfo("Failed type convert", sinfo, undefined)})`
            return vtype.tkeystr.startsWith("Some") ? (isnot ? mfail : val) : (isnot ? val : mfail);
        }
        else {
            const emsg = this.getErrorInfo(isnot ? "expected None but got Some" : "expected Some but got None", sinfo, undefined);
            return val + (isnot ? `._$asNotSome(${emsg})` : `._$asSome(${emsg})`);
        }
    }

    private emitITestAsConvert_Ok(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
        const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);

        if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            const mfail = `_$abort(${this.getErrorInfo("Failed type convert", sinfo, undefined)})`
            return vtype.tkeystr === oktype.tkeystr ? (isnot ? mfail : val) : (isnot ? val : mfail);
        }
        else {
            const emsg = this.getErrorInfo(isnot ? "expected Err but got Ok" : "expected Ok but got Err", sinfo, undefined);
            return val + (isnot ? "._$asNotOk" : "._$asOk") + `(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oktype)}, ${emsg})`;
        }
    }

    private emitITestAsConvert_Fail(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
        const failtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getFailType(), (vtype as NominalTypeSignature).alltermargs);

        if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            const mfail = `_$abort(${this.getErrorInfo("Failed type convert", sinfo, undefined)})`
            return vtype.tkeystr === failtype.tkeystr ? (isnot ? mfail : val) : (isnot ? val : mfail);
        }
        else {
            const emsg = this.getErrorInfo(isnot ? "expected Ok but got Err" : "expected Err but got Ok", sinfo, undefined);
            return val + (isnot ? "._$asNotFail" : "._$asFail") + `(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), failtype)}, ${emsg})`;
        }
    }

    private emitITestAsConvert_Type(sinfo: SourceInfo, val: string, vtype: TypeSignature, oftype: TypeSignature, isnot: boolean): string {
        if(vtype instanceof EListTypeSignature) {
            const mfail = `_$abort(${this.getErrorInfo("Failed type convert", sinfo, undefined)})`;

            if(!(oftype instanceof EListTypeSignature)) {
                return isnot ? val : mfail;
            }
            else {
                return vtype.tkeystr === oftype.tkeystr ? (isnot ? mfail : val) : (isnot ? val : mfail);
            }
        }
        else if(EmitNameManager.isUniqueTypeForSubtypeChecking(vtype)) {
            const mfail = `_$abort(${this.getErrorInfo("Failed type convert", sinfo, undefined)})`;

            if(EmitNameManager.isUniqueTypeForSubtypeChecking(oftype)) {
                return vtype.tkeystr === oftype.tkeystr ? (isnot ? mfail : val) : (isnot ? val : mfail);
            }
            else {
                if(!EmitNameManager.isMethodCallObjectRepr(vtype)) {
                    const asop = isnot ? "_$asNotSubtype" : "_$asSubtype";
                    return `${val}.${asop}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype as NominalTypeSignature)}, ${this.getErrorInfo("Failed type convert", sinfo, undefined)})`; 
                }                    
                else {
                    if(EmitNameManager.isNoneType(vtype)) {
                        if(EmitNameManager.isOptionType(oftype)) {
                            return isnot ? mfail : val;
                        }
                        else {
                            return isnot ? val : mfail;
                        }
                    }
                    else {
                        const asop = isnot ? "_$fasNotSubtype" : "_$fasSubtype";
                        return `${asop}(${val}, ${EmitNameManager.generateAccessorForTypeKey(this.currentns as NamespaceDeclaration, vtype as NominalTypeSignature)}, ${EmitNameManager.generateAccessorForTypeKey(this.currentns as NamespaceDeclaration, oftype as NominalTypeSignature)}, ${this.getErrorInfo("Failed type convert", sinfo, undefined)})`;
                    }
                }
            }
        }
        else {
            if(EmitNameManager.isUniqueTypeForSubtypeChecking(oftype)) {
                const emsg = this.getErrorInfo(isnot ? `expected different type than ${oftype.tkeystr}` : `expected type ${oftype.tkeystr}`, sinfo, undefined);

                const asop = isnot ? "_$asNot" : "_$as";
                return `${val}.${asop}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype as NominalTypeSignature)}, ${emsg})`;
            }
            else {
                const emsg = this.getErrorInfo(isnot ? `expected not subtype of ${oftype.tkeystr}` : `expected subtytype of ${oftype.tkeystr}`, sinfo, undefined);

                if(EmitNameManager.isOptionType(oftype)) {
                    const asop = isnot ? "_$asNotOptionSubtype" : "_$asOptionSubtype";
                    return `${val}.${asop}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype as NominalTypeSignature)}, ${emsg})`;
                }
                else {
                    const asop = isnot ? "_$asNotSubtype" : "_$asSubtype";
                    return `${val}.${asop}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype as NominalTypeSignature)}, ${emsg})`;
                }
            }
        }
    }

    private processITestAsConvert(sinfo: SourceInfo, val: string, vtype: TypeSignature, tt: ITest, negatecondition: boolean): string {
        const vvtype = this.tproc(vtype);
        
        if(tt instanceof ITestType) {
            return this.emitITestAsConvert_Type(sinfo, val, vvtype, this.tproc(tt.ttype), negatecondition);
        }
        else {
            if(tt instanceof ITestNone) {
                return this.emitITestAsConvert_None(sinfo, val, vvtype, negatecondition);
            }
            else if(tt instanceof ITestSome) {
                return this.emitITestAsConvert_Some(sinfo, val, vvtype, negatecondition);
            }
            else if(tt instanceof ITestOk) {
                return this.emitITestAsConvert_Ok(sinfo, val, vvtype, negatecondition);
            }
            else {
                assert(tt instanceof ITestFail, "missing case in ITest");
                return this.emitITestAsConvert_Fail(sinfo, val, vvtype, negatecondition);
            }
        }
    }

    private emitLiteralNoneExpression(): string {
        return "_$None";
    }

    private emitLiteralBoolExpression(exp: LiteralSimpleExpression): string {
        return exp.value;
    }

    private emitLiteralNatExpression(exp: LiteralSimpleExpression): string {
        return `${exp.value.slice(exp.value.startsWith("+") ? 1 : 0, -1)}n`;
    }

    private emitLiteralIntExpression(exp: LiteralSimpleExpression): string {
        return `${exp.value.slice(exp.value.startsWith("+") ? 1 : 0, -1)}n`;
    }

    private emitLiteralBigNatExpression(exp: LiteralSimpleExpression): string {
        return `${exp.value.slice(exp.value.startsWith("+") ? 1 : 0, -1)}n`;
    }

    private emitLiteralBigIntExpression(exp: LiteralSimpleExpression): string {
        return `${exp.value.slice(exp.value.startsWith("+") ? 1 : 0, -1)}n`;
    }

    private emitLiteralRationalExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- Rational");
    }

    private emitLiteralFloatExpression(exp: LiteralSimpleExpression): string {
        return exp.value.slice(0, -1);
    }
    
    private emitLiteralDecimalExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- Decimal");
    }
    
    private emitLiteralDecimalDegreeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DecimalDegree");
    }
    
    private emitLiteralLatLongCoordinateExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- LatLongCoordinate");
    }
    
    private emitLiteralComplexNumberExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- ComplexNumber");
    }
    
    private emitLiteralByteBufferExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- ByteBuffer");
    }
    
    private emitLiteralUUIDv4Expression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- UUIDv4");
    }
    
    private emitLiteralUUIDv7Expression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- UUIDv7");
    }
    
    private emitLiteralSHAContentHashExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- SHAContentHash");
    }
    
    private emitLiteralTZDateTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DateTime");
    }
    
    private emitLiteralTAITimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- TAIDateTime");
    }
    
    private emitLiteralPlainDateExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- PlainDate");
    }
    
    private emitLiteralPlainTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- PlainTime");
    }
    
    private emitLiteralLogicalTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- LogicalTime");
    }
    
    private emitLiteralISOTimeStampExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- ISOTimeStamp");
    }
    
    private emitLiteralDeltaDateTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaDateTime");
    }
    
    private emitLiteralDeltaISOTimeStampExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaISOTimeStamp");
    }
    
    private emitLiteralDeltaSecondsExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaSeconds");
    }
    
    private emitLiteralDeltaLogicalExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaLogical");
    }
    
    private emitLiteralUnicodeRegexExpression(exp: LiteralRegexExpression): string {
        const restr = exp.value.replace(/\"/g, "\\\"");
        return `"${restr}"`;
    }
    
    private emitLiteralCRegexExpression(exp: LiteralRegexExpression): string {
        const restr = exp.value.replace(/'/g, "\\'");
        return `'${restr}'`;
    }
    
    private emitLiteralCCharExpression(exp: LiteralSimpleExpression): string {
        if(JSCodeFormatter.isEscapeFreeString(exp.resolvedValue)) {
            return `"${exp.resolvedValue}"`;
        }
        else {
            return `decodeURI(${JSCodeFormatter.emitEscapedString(exp.resolvedValue)})`;
        }    
    }
        
    private emitLiteralUnicodeCharExpression(exp: LiteralSimpleExpression): string {
        if(JSCodeFormatter.isEscapeFreeString(exp.resolvedValue)) {
            return `"${exp.resolvedValue}"`;
        }
        else {
            return `decodeURI(${JSCodeFormatter.emitEscapedString(exp.resolvedValue)})`;
        }
    }

    private emitLiteralStringExpression(exp: LiteralSimpleExpression): string {
        if(JSCodeFormatter.isEscapeFreeString(exp.resolvedValue)) {
            return `"${exp.resolvedValue}"`;
        }
        else {
            return `decodeURI(${JSCodeFormatter.emitEscapedString(exp.resolvedValue)})`;
        }
    }
    
    private emitLiteralCStringExpression(exp: LiteralSimpleExpression): string {
        if(JSCodeFormatter.isEscapeFreeString(exp.resolvedValue)) {
            return `"${exp.resolvedValue}"`;
        }
        else {
            return `decodeURI(${JSCodeFormatter.emitEscapedString(exp.resolvedValue)})`;
        }
    }
    
    private emitLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression, toplevel: boolean): string {
        const taccess = EmitNameManager.generateAccessorForSpecialTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.constype) as NominalTypeSignature);
        return `${taccess}(${this.emitExpression(exp.value, true)})`;
    }
        
    private emitHasEnvValueExpression(exp: AccessEnvValueExpression): string {
        assert(false, "Not implemented -- HasEnvValue");
    }
            
    private emitAccessEnvValueExpression(exp: AccessEnvValueExpression): string {
        assert(false, "Not implemented -- AccessEnvValue");
    }
            
    private emitTaskAccessInfoExpression(exp: TaskAccessInfoExpression): string {
        assert(false, "Not implemented -- TaskAccessInfo");
    }

    private emitAccessNamespaceConstantExpression(exp: AccessNamespaceConstantExpression): string {
        const cns = EmitNameManager.resolveNamespaceDecl(this.assembly, exp.ns);
        const cdecl = cns.consts.find((c) => c.name === exp.name) as NamespaceConstDecl;
        return EmitNameManager.generateAccssorNameForNamespaceConstant(this.getCurrentNamespace(), cns, cdecl);
    }
    
    private emitAccessStaticFieldExpression(exp: AccessStaticFieldExpression): string {
        const ctt = this.tproc(exp.resolvedDeclType as TypeSignature) as NominalTypeSignature;

        const cdecl = ctt.decl.consts.find((c) => c.name === exp.name) as ConstMemberDecl;
        return EmitNameManager.generateAccssorNameForTypeConstant(this.getCurrentNamespace(), ctt, cdecl);
    }
    
    private emitAccessEnumExpression(exp: AccessEnumExpression): string {
        return EmitNameManager.generateAccssorNameForEnumMember(this.getCurrentNamespace(), exp.stype as NominalTypeSignature, exp.name);
    }

    private emitAccessVariableExpression(exp: AccessVariableExpression): string {
        let aname = exp.srcname;
        
        //handle special names here)
        if(aname === "this") {
            return "$this$";
        }

        if(exp.specialaccess.length !== 0) {
            for(let i = 0; i < exp.specialaccess.length; ++i) {
                if(exp.specialaccess[i].specialaccess !== undefined) {
                    aname = `${aname}.${exp.specialaccess[i].specialaccess}`;
                }
            }
        }

        return aname;
    }
    
    private processEmitListConstructor(ttype: TypeSignature, args: ArgumentValue[]): string {
        const argc = args.length;
        const allsimple = args.every((aa) => aa instanceof PositionalArgumentValue);

        const coreprefix = this.getCurrentNamespace().fullnamespace.ns[0] !== "Core" ? "$Core." : "";

        if(argc === 0) {
            return `${coreprefix}ListOps.s_list_create_empty["<${ttype.tkeystr}>"]()`;
        }
        else if(argc <= 6 && allsimple) {
            let opr: string;

            if(argc === 1) {
                opr = "s_list_create_1";
            }
            else if(argc === 2) {
                opr = "s_list_create_2";
            }
            else if(argc === 3) {
                opr = "s_list_create_3";
            }
            else if(argc === 4) {
                opr = "s_list_create_4";
            }
            else if(argc === 5) {
                opr = "s_list_create_5";
            }
            else {
                opr = "s_list_create_6";
            }

            const llargs = args.map((ee) => this.emitExpression(ee.exp, true));
            return `${coreprefix}ListOps.${opr}["<${ttype.tkeystr}>"](${llargs.join(", ")})`;
        }
        else {
            if(argc === 1) {
                //a spread of a single thing -- maybe a list or other special case we want to do
                assert(false, "Not implemented -- List values");
            }
            else {
                assert(false, "Not implemented -- List values"); //TODO: need to implement list in Bosque core + have way well known way to call constructor here!!!!
            }
        }
    }

    private processEmitMapConstructor(ktype: TypeSignature, vtype: TypeSignature, args: ArgumentValue[]): string {
        const argc = args.length;
        const allsimple = args.every((aa) => aa instanceof PositionalArgumentValue);

        const coreprefix = this.getCurrentNamespace().fullnamespace.ns[0] !== "Core" ? "$Core." : "";

        if(argc === 0) {
            return `${coreprefix}MapOps.s_map_create_empty["<${ktype.tkeystr}, ${vtype.tkeystr}>"]()`;
        }
        else if(argc <= 2 && allsimple) {
            let opr: string;

            if(argc === 1) {
                opr = "s_map_create_1";
            }
            else {
                opr = "s_map_create_2";
            }

            const llargs = args.map((ee) => this.emitExpression(ee.exp, true));
            return `${coreprefix}MapOps.${opr}["<${ktype.tkeystr}, ${vtype.tkeystr}>"](${llargs.join(", ")})`;
        }
        else {
            if(argc === 1) {
                //a spread of a single thing -- maybe a list or other special case we want to do
                assert(false, "Not implemented -- Map values");
            }
            else {
                assert(false, "Not implemented -- Map values"); //TODO: need to implement list in Bosque core + have way well known way to call constructor here!!!!
            }
        }
    }

    //
    // We will need to add processEmitUnicodeCharBufferConstructor and processEmitCCharBufferConstructor as well
    // I can't think of any other way to handle this - even though they should only need to operate with c++ bit ops
    //

    private emitCollectionConstructor(cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): string {
        const ctype = this.tproc(exp.ctype) as NominalTypeSignature;

        if(cdecl instanceof ListTypeDecl) {
            const ttype = ctype.alltermargs[0];
            return this.processEmitListConstructor(ttype, exp.args.args);
        }
        else if(cdecl instanceof MapTypeDecl) {
            const ktype = ctype.alltermargs[0];
            const vtype = ctype.alltermargs[1];
            return this.processEmitMapConstructor(ktype, vtype, exp.args.args);
        }
        else {
            assert(false, "Unknown collection type -- emitCollectionConstructor");
        }
    }

    private emitSpecialConstructableConstructor(cdecl: ConstructableTypeDecl, exp: ConstructorPrimaryExpression, toplevel: boolean): string {
        const eargs = exp.args.args.map((ee) => this.emitExpression(ee.exp, true));
        const taccess = EmitNameManager.generateAccessorForSpecialTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.ctype) as NominalTypeSignature);
        
        return `${taccess}(${eargs.join(", ")})`;
    }

    private emitTypeDeclConstructor(cdecl: TypedeclTypeDecl, exp: ConstructorPrimaryExpression, toplevel: boolean): string {
        const earg = this.emitExpression(exp.args.args[0].exp, true);
        const taccess = EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.ctype) as NominalTypeSignature);
            
        return `${taccess}(${earg})`;
    }

    private emitStandardConstructor(exp: ConstructorPrimaryExpression): string {
        const aargs: string[] = [];
        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            const ii = exp.shuffleinfo[i];
            if(ii[0] === -1) {
                aargs.push("undefined");
            }
            else {
                const aaexp = this.emitExpression(exp.args.args[ii[0]].exp, true);
                aargs.push(aaexp);
            }
        }

        const taccess = EmitNameManager.generateAccessorForStdTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.ctype) as NominalTypeSignature);

        return `${taccess}(${aargs.join(", ")})`;
    }

    private emitConstructorPrimaryExpression(exp: ConstructorPrimaryExpression, toplevel: boolean): string {
        const ctype = exp.ctype as NominalTypeSignature;
        const decl = ctype.decl;
        if(decl instanceof AbstractCollectionTypeDecl) {
            return this.emitCollectionConstructor(decl, exp);
        }
        else if(decl instanceof ConstructableTypeDecl) {
            return this.emitSpecialConstructableConstructor(decl, exp, toplevel);
        }
        else if(decl instanceof TypedeclTypeDecl) {
            return this.emitTypeDeclConstructor(decl, exp, toplevel);
        }
        else {
            return this.emitStandardConstructor(exp);
        }
    }
    
    private emitConstructorEListExpression(exp: ConstructorEListExpression): string {
        const vals = exp.args.args.map((ee, ii) => {
            return this.emitExpression(ee.exp, true);
        });

        return `[${vals.join(", ")}]`;
    }
    
    private emitConstructorLambdaExpression(exp: ConstructorLambdaExpression): string {
        const params = `(${exp.invoke.params.map((pp) => pp.name).join(", ")})`;

        const optrefv = exp.invoke.params.find((pp) => pp.isRefParam);
        const body = this.emitBodyImplementation(exp.invoke.body, false, [], [], [], optrefv !== undefined ? optrefv.name : undefined, undefined, new JSCodeFormatter(undefined));

        return `${params} => ${body}`;
    }

    private emitLetExpression(exp: LetExpression): string {
        assert(false, "Not implemented -- Let");
    }

    private emitLambdaInvokeExpression(exp: LambdaInvokeExpression): string {
        const argl: string[] = [];
        for(let i = 0; i < exp.arginfo.length; ++i) {
            const arg = exp.args.args[i].exp;
            const aaexp = this.emitExpression(arg, true);
            argl.push(aaexp);
        }

        if(exp.restinfo !== undefined) {
            const restl: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                const rri = exp.restinfo[i];
                if(!rri[1]) {
                    restl.push(exp.args.args[rri[0]]);
                }
                else {
                    assert(false, "Not implemented -- LambdaFunction -- spread into rest");
                }
            }

            const rtype = exp.resttype as NominalTypeSignature;
            if(rtype.decl instanceof ListTypeDecl) {
                argl.push(this.processEmitListConstructor(rtype.alltermargs[0], restl));
            }
            else {
                assert(false, "Not implemented -- LambdaFunction -- rest");
            }
        }

        return `${exp.name}(${argl.join(", ")})`;
    }

    private emitSpecialConstructorExpression(exp: SpecialConstructorExpression, toplevel: boolean): string {
        const val = this.emitExpression(exp.arg, toplevel);
        const taccess = EmitNameManager.generateAccessorForSpecialTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.constype as TypeSignature) as NominalTypeSignature);

        return `${taccess}(${val})`;
    }
    
    private emitCallNamespaceFunctionExpression(exp: CallNamespaceFunctionExpression): string {
        const cns = EmitNameManager.resolveNamespaceDecl(this.assembly, exp.ns);
        const ffinv = cns.functions.find((f) => f.name === exp.name) as NamespaceFunctionDecl;

        const argl: string[] = [];
        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            const ii = exp.shuffleinfo[i];
            if(ii[0] === -1) {
                argl.push("undefined");
            }
            else {
                const aaexp = this.emitExpression(exp.args.args[ii[0]].exp, true);
                argl.push(aaexp);
            }
        }

        if(exp.restinfo !== undefined) {
            const restl: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                const rri = exp.restinfo[i];
                if(!rri[1]) {
                    restl.push(exp.args.args[rri[0]]);
                }
                else {
                    assert(false, "Not implemented -- CallNamespaceFunction -- spread into rest");
                }
            }

            const rtype = exp.resttype as NominalTypeSignature;
            if(rtype.decl instanceof ListTypeDecl) {
                argl.push(this.processEmitListConstructor(rtype.alltermargs[0], restl));
            }
            else {
                assert(false, "Not implemented -- CallNamespaceFunction -- rest");
            }
        }

        return `${EmitNameManager.generateAccssorNameForNamespaceFunction(this.getCurrentNamespace(), cns, ffinv, exp.terms.map((tt) => this.tproc(tt)))}(${argl.join(", ")})`;
    }
    
    private emitCallTypeFunctionExpressionSpecial(exp: CallTypeFunctionExpression, rtrgt: NominalTypeSignature): string {
        const taccess = EmitNameManager.generateAccessorForSpecialTypeConstructor(this.getCurrentNamespace(), rtrgt);

        const sexp = (exp.shuffleinfo[0][1] as TypeSignature).tkeystr
        const simple = (sexp === "CString" || sexp === "String");

        if(simple) {
            return `${taccess}(${this.emitExpression(exp.args.args[0].exp, true)})`;
        }
        else {
            return `${taccess}(${this.emitExpression(exp.args.args[0].exp, false)}.value)`;
        }
    }

    private emitCallTypeFunctionExpression(exp: CallTypeFunctionExpression): string {
        const rtrgt = (this.tproc(exp.resolvedDeclType as TypeSignature) as NominalTypeSignature);

        if(exp.isSpecialCall) {
            return this.emitCallTypeFunctionExpressionSpecial(exp, rtrgt);
        }
        else {
            const fdecl = rtrgt.decl.functions.find((m) => m.name === exp.name) as FunctionInvokeDecl;

            const argl: string[] = [];
            for(let i = 0; i < exp.shuffleinfo.length; ++i) {
                const ii = exp.shuffleinfo[i];
                if(ii[0] === -1) {
                    argl.push("undefined");
                }
                else {
                    const aaexp = this.emitExpression(exp.args.args[ii[0]].exp, true);
                    argl.push(aaexp);
                }
            }

            if(exp.restinfo !== undefined) {
                const restl: ArgumentValue[] = [];

                for(let i = 0; i < exp.restinfo.length; ++i) {
                    const rri = exp.restinfo[i];
                    if(!rri[1]) {
                        restl.push(exp.args.args[rri[0]]);
                    }
                    else {
                        assert(false, "Not implemented -- CallNamespaceFunction -- spread into rest");
                    }
                }

                const rtype = exp.resttype as NominalTypeSignature;
                if(rtype.decl instanceof ListTypeDecl) {
                    argl.push(this.processEmitListConstructor(rtype.alltermargs[0], restl));
                }
                else {
                    assert(false, "Not implemented -- CallNamespaceFunction -- rest");
                }
            }

            return `${EmitNameManager.generateAccssorNameForTypeFunction(this.getCurrentNamespace(), rtrgt, fdecl, exp.terms.map((tt) => this.tproc(tt)))}(${argl.join(", ")})`;
        }
    }
    
    private emitLogicActionAndExpression(exp: LogicActionAndExpression): string {
        const exps = exp.args.map((ee) => this.emitExpression(ee, true));
        return `[${exps.join(", ")}].every((ee) => ee)`;
    }
    
    private emitLogicActionOrExpression(exp: LogicActionOrExpression): string {
        const exps = exp.args.map((ee) => this.emitExpression(ee, true));
        return `(![${exps.join(", ")}].every((ee) => !ee))`;
    }
    
    private emitParseAsTypeExpression(exp: ParseAsTypeExpression, toplevel: boolean): string {
        return this.emitExpression(exp.exp, toplevel);
    }

    private emitSafeConvertExpression(exp: SafeConvertExpression, toplevel: boolean): string {
        return this.emitExpression(exp.exp, toplevel);
    }

    private emitCreateDirectExpression(exp: CreateDirectExpression, toplevel: boolean): string {
        const eexp = this.emitExpression(exp.exp, true);
        const consop = EmitNameManager.generateAccessorForSpecialTypeConstructor(this.currentns as NamespaceDeclaration, this.tproc(exp.trgttype) as NominalTypeSignature);

        return `${consop}(${eexp})`;
    }
    
    private emitPostfixAccessFromName(val: string, exp: PostfixAccessFromName): string {
        const fdecl = exp.fieldDecl as MemberFieldDecl;
        return `${val}.${fdecl.name}`;
    }

    private emitPostfixProjectFromNames(val: string, exp: PostfixProjectFromNames): string {
        assert(false, "Not Implemented -- emitPostfixProjectFromNames");
    }

    private emitPostfixAccessFromIndex(val: string, exp: PostfixAccessFromIndex): string {
        return `${val}[${exp.idx}]`;
    }

    private emitPostfixIsTest(val: string, exp: PostfixIsTest): string {
        return this.processITestAsTest(val, this.tproc(exp.getRcvrType()), exp.ttest);
    }

    private emitPostfixAsConvert(val: string, exp: PostfixAsConvert): string {
        return this.processITestAsConvert(exp.sinfo, val, this.tproc(exp.getRcvrType()), exp.ttest, exp.ttest.isnot);
    }

    private emitPostfixAssignFields(val: string, exp: PostfixAssignFields): string {
        const updatecalls = exp.updates.map((upd) => upd[0] + `: (($${upd[0]}) => { return ` + this.emitExpression(upd[1], true) + `; })($$v$$.${upd[0]})`).join(", ");

        return `((($$v$$) => $$v$$.$update({ ${updatecalls} }))(${val}))`;
    }

    private emitResolvedPostfixInvoke(val: string, exp: PostfixInvoke): string {
        const rtrgt = (this.tproc(exp.resolvedTrgt as TypeSignature) as NominalTypeSignature);
        const mdecl = rtrgt.decl.methods.find((m) => m.name === exp.name) as MethodDecl;

        const argl: string[] = [];
        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            const ii = exp.shuffleinfo[i];
            if(ii[0] === -1) {
                argl.push("undefined");
            }
            else {
                const aaexp = this.emitExpression(exp.args.args[ii[0]].exp, true);
                argl.push(aaexp);
            }
        }

        if(exp.restinfo !== undefined) {
            const restl: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                const rri = exp.restinfo[i];
                if(!rri[1]) {
                    restl.push(exp.args.args[rri[0]]);
                }
                else {
                    assert(false, "Not implemented -- CallPostfixInvoken -- spread into rest");
                }
            }

            const rtype = exp.resttype as NominalTypeSignature;
            if(rtype.decl instanceof ListTypeDecl) {
                argl.push(this.processEmitListConstructor(rtype.alltermargs[0], restl));
            }
            else {
                assert(false, "Not implemented -- CallPostfixInvoken -- rest");
            }
        }

        if(EmitNameManager.isMethodCallObjectRepr(rtrgt)) {
            if(exp.terms.length === 0) {
                return `${val}.${EmitNameManager.generateAccssorNameForMethodImplicit(this.getCurrentNamespace(), rtrgt, mdecl, exp.terms.map((tt) => this.tproc(tt)))}(${argl.join(", ")})`;
            }
            else {
                return `${val}.$scall("${exp.name}", "${EmitNameManager.generateTermKeyFromTermTypes(exp.terms.map((tt) => this.tproc(tt)))}"${argl.length !== 0 ? ", " : ""}${argl.join(", ")})`; 
            }
        }
        else {
            return `${EmitNameManager.generateAccssorNameForMethodFull(this.getCurrentNamespace(), rtrgt, mdecl, exp.terms.map((tt) => this.tproc(tt)))}.call(${val}${argl.length !== 0 ? ", " : ""}${argl.join(", ")})`;
        }
    }

    private emitVirtualPostfixInvoke(val: string, exp: PostfixInvoke): string {
        assert(false, "Not Implemented -- emitResolvedPostfixInvoke Virtual");
    }

    private emitPostfixInvoke(val: string, exp: PostfixInvoke): string {
        if(exp.resolvedTrgt !== undefined) {
            return this.emitResolvedPostfixInvoke(val, exp);
        }
        else {
            return this.emitVirtualPostfixInvoke(val, exp);
        }
    }

    private emitPostfixLiteralKeyAccess(val: string, exp: PostfixLiteralKeyAccess): string {
        assert(false, "Not Implemented -- emitPostfixLiteralKeyAccess");
    }

    private emitPostfixOp(exp: PostfixOp, toplevel: boolean): string {
        let eexp = this.emitExpression(exp.rootExp, false);
    
        for(let i = 0; i < exp.ops.length; ++i) {
            const op = exp.ops[i];
            
            switch(op.tag) {
                case PostfixOpTag.PostfixAccessFromName: {
                    eexp = this.emitPostfixAccessFromName(eexp, op as PostfixAccessFromName);
                    break;
                }
                case PostfixOpTag.PostfixProjectFromNames: {
                    eexp = this.emitPostfixProjectFromNames(eexp, op as PostfixProjectFromNames);
                    break;
                }
                case PostfixOpTag.PostfixAccessFromIndex: {
                    eexp = this.emitPostfixAccessFromIndex(eexp, op as PostfixAccessFromIndex);
                    break;
                }
                case PostfixOpTag.PostfixIsTest: {
                    eexp = this.emitPostfixIsTest(eexp, op as PostfixIsTest);
                    break;
                }
                case PostfixOpTag.PostfixAsConvert: {
                    eexp = this.emitPostfixAsConvert(eexp, op as PostfixAsConvert);
                    break;
                }
                case PostfixOpTag.PostfixAssignFields: {
                    eexp = this.emitPostfixAssignFields(eexp, op as PostfixAssignFields);
                    break;
                }
                case PostfixOpTag.PostfixInvoke: {
                    eexp = this.emitPostfixInvoke(eexp, op as PostfixInvoke);
                    break;
                }
                case PostfixOpTag.PostfixLiteralKeyAccess: {
                    eexp = this.emitPostfixLiteralKeyAccess(eexp, op as PostfixLiteralKeyAccess);
                    break;
                }
                default: {
                    assert(op.tag === PostfixOpTag.PostfixError, "Unknown postfix op");
                    eexp += "[ERROR POSTFIX OP]";
                }
            }
        }

        return eexp;
    }

    private emitPrefixNotOpExpression(exp: PrefixNotOpExpression, toplevel: boolean): string {
        const optype = exp.opertype as TypeSignature;

        if(EmitNameManager.isPrimitiveType(optype)) {
            const eexp = `!${this.emitExpression(exp.exp, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const eexp = this.emitExpression(exp.exp, true);
            const cc = EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), exp.getType() as NominalTypeSignature);

            return `_$not(${eexp}, ${cc})`;
        }
    }

    private emitPrefixNegateOrPlusOpExpression(exp: PrefixNegateOrPlusOpExpression, toplevel: boolean): string {
        if(exp.op === "+") {
            return this.emitExpression(exp.exp, toplevel);
        }
        else {
            const optype = exp.opertype as TypeSignature;
            
            if(EmitNameManager.isPrimitiveType(optype)) {
                const eexp = `-${this.emitExpression(exp.exp, false)}`;
                return !toplevel ? `(${eexp})` : eexp;
            }
            else {
                const eexp = this.emitExpression(exp.exp, true);
                const cc = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.getType()) as NominalTypeSignature)}`;

                const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
                return `_$negate.${optype}(${eexp}, ${cc})`;
            }
        }
    }

    private emitBinAddExpression(exp: BinAddExpression, toplevel: boolean): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
        const etype = this.tproc(exp.getType());

        let ccepr = "";
        if(!EmitNameManager.isPrimitiveType(etype)) {
            ccepr = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), etype as NominalTypeSignature)}`;
        }

        return `_$add.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}${ccepr})`;
    }

    private emitBinSubExpression(exp: BinSubExpression, toplevel: boolean): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
        const etype = this.tproc(exp.getType());

        let ccepr = "";
        if(!EmitNameManager.isPrimitiveType(etype)) {
            ccepr = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), etype as NominalTypeSignature)}`;
        }

        return `_$sub.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}${ccepr})`;
    }
    
    private emitBinMultExpression(exp: BinMultExpression, toplevel: boolean): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
        const etype = this.tproc(exp.getType());

        let ccepr = "";
        if(!EmitNameManager.isPrimitiveType(etype)) {
            ccepr = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), etype as NominalTypeSignature)}`;
        }

        return `_$mult.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}${ccepr})`;
    }
    
    private emitBinDivExpression(exp: BinDivExpression, toplevel: boolean): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
        const etype = this.tproc(exp.getType());

        let ccepr = "";
        if(!EmitNameManager.isPrimitiveType(etype)) {
            ccepr = `, ${EmitNameManager.generateAccessorForTypedeclTypeConstructor(this.getCurrentNamespace(), etype as NominalTypeSignature)}`;
        }

        return `_$div.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}${ccepr})`;
    }
    
    private emitBinKeyEqExpression(exp: BinKeyEqExpression, toplevel: boolean): string {
        const kcop = exp.operkind;

        if(kcop === "lhsnone") {
            return `${this.emitExpression(exp.rhs, false)}._$isNone()`;
        }
        else if(kcop === "rhsnone") {
            return `${this.emitExpression(exp.lhs, false)}._$isNone()`;
        }
        else if(kcop === "lhskeyeqoption") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkeqopt.${optype}(${this.emitExpression(exp.rhs, true)}, ${this.emitExpression(exp.lhs, true)})`;
        }
        else if(kcop === "rhskeyeqoption") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkeqopt.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
        else if(kcop === "stricteq") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkeq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitBinKeyNeqExpression(exp: BinKeyNeqExpression, toplevel: boolean): string {
        const kcop = exp.operkind;

        if(kcop === "lhsnone") {
            return `${this.emitExpression(exp.rhs, false)}._$isNotNone()`;
        }
        else if(kcop === "rhsnone") {
            return `${this.emitExpression(exp.lhs, false)}._$isNotNone()`;
        }
        else if(kcop === "lhskeyeqoption") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkneqopt.${optype}(${this.emitExpression(exp.rhs, true)}, ${this.emitExpression(exp.lhs, true)})`;
        }
        else if(kcop === "rhskeyeqoption") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkneqopt.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
        else if(kcop === "stricteq") {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fkneq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitKeyCompareEqExpression(exp: KeyCompareEqExpression, toplevel: boolean): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.optype as TypeSignature));
        return `_$fkeq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitKeyCompareLessExpression(exp: KeyCompareLessExpression, toplevel: boolean): string {
        const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.optype as TypeSignature));
        return `_$fkless.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitNumericEqExpression(exp: NumericEqExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} === ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumeq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;            
        }
    }

    private emitNumericNeqExpression(exp: NumericNeqExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} !== ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `(!_$fnumeq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}))`;
        }
    }
    
    private emitNumericLessExpression(exp: NumericLessExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} < ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumless.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
    }
    
    private emitNumericLessEqExpression(exp: NumericLessEqExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} <= ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumlesseq.${optype}(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        }
    }
    
    private emitNumericGreaterExpression(exp: NumericGreaterExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} > ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumless.${optype}(${this.emitExpression(exp.rhs, true)}, ${this.emitExpression(exp.lhs, true)})`;
        }
    }

    private emitNumericGreaterEqExpression(exp: NumericGreaterEqExpression, toplevel: boolean): string {
        if(EmitNameManager.isPrimitiveType(this.tproc(exp.lhs.getType() as TypeSignature))) {
            const eexp = `${this.emitExpression(exp.lhs, false)} >= ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(exp.opertype as TypeSignature));
            return `_$fnumlesseq.${optype}(${this.emitExpression(exp.rhs, true)}, ${this.emitExpression(exp.lhs, true)})`;
        }
    }

    private emitBinLogicAndExpression(exp: BinLogicAndExpression, toplevel: boolean): string {
        let ee1 = this.emitExpression(exp.lhs, !exp.purebool);
        let ee2 = this.emitExpression(exp.rhs, !exp.purebool);

        if(!exp.purebool) {
            ee1 = `_$bval${ee1}`;
            ee2 = `_$bval${ee2}`;
        }
        
        const eexp = `${ee1} && ${ee2}`;
        return !toplevel && exp.purebool ? `(${eexp})` : eexp;
    }

    private emitBinLogicOrExpression(exp: BinLogicOrExpression, toplevel: boolean): string {
        let ee1 = this.emitExpression(exp.lhs, !exp.purebool);
        let ee2 = this.emitExpression(exp.rhs, !exp.purebool);

        if(!exp.purebool) {
            ee1 = `_$bval${ee1}`;
            ee2 = `_$bval${ee2}`;
        }

        const eexp = `${ee1} || ${ee2}`;
        return !toplevel && exp.purebool ? `(${eexp})` : eexp;
    }

    private emitBinLogicImpliesExpression(exp: BinLogicImpliesExpression, toplevel: boolean): string {
        let ee1 = this.emitExpression(exp.lhs, !exp.purebool);
        let ee2 = this.emitExpression(exp.rhs, !exp.purebool);

        if(!exp.purebool) {
            ee1 = `_$bval${ee1}`;
            ee2 = `_$bval${ee2}`;
        }

        const eeexp = `!${ee1} || ${ee2}`;
        return !toplevel && exp.purebool ? `(${eeexp})` : eeexp;
    }

    private emitBinLogicIFFExpression(exp: BinLogicIFFExpression, toplevel: boolean): string {
        let ee1 = this.emitExpression(exp.lhs, !exp.purebool);
        let ee2 = this.emitExpression(exp.rhs, !exp.purebool);

        if(!exp.purebool) {
            ee1 = `_$bval${ee1}`;
            ee2 = `_$bval${ee2}`;
        }

        const eexp = `${ee1} === ${ee2}`;
        return !toplevel && exp.purebool ? `(${eexp})` : eexp;
    }
    
    private emitMapEntryConstructorExpression(exp: MapEntryConstructorExpression): string {
        let ekey = this.emitExpression(exp.kexp, true);
        let evalue = this.emitExpression(exp.vexp, true);

        const cname = EmitNameManager.generateAccessorForSpecialTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.ctype as TypeSignature) as NominalTypeSignature);
        return `${cname}(${ekey}, ${evalue})`;
    }

    private emitIfExpression(exp: IfExpression, toplevel: boolean): string {
        const texp = this.emitExpression(exp.trueValue, false);
        const fexp = this.emitExpression(exp.falseValue, false);

        if(exp.test.itestopt === undefined) {
            const purebool = this.tproc(exp.test.exp.getType()).tkeystr === "Bool";
            let test = this.emitExpression(exp.test.exp, !purebool);
            if(!purebool) {
                test = `_$bval(${test})`;
            }

            const eexp = `${test} ? ${texp} : ${fexp}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            const vval = this.emitExpression(exp.test.exp, false);
        
            if(exp.binder === undefined) {
                const ttest = this.processITestAsTest(vval, exp.test.exp.getType(), exp.test.itestopt);
                const eexp = `${ttest} ? ${texp} : ${fexp}`;
                return !toplevel ? `(${eexp})` : eexp;
            }
            else {
                //TODO: this setup means that if we shaddow this binder then we don't have proper stack discipline in the code
                const bbn = exp.binder.srcname;
                this.bindernames.add(bbn);

                const ttest = this.processITestAsTest(vval, exp.test.exp.getType(), exp.test.itestopt);
                const bexptrue = this.processITestAsConvert(exp.sinfo, vval, exp.test.exp.getType(), exp.test.itestopt, exp.test.itestopt.isnot);
                const bexpfalse = this.processITestAsConvert(exp.sinfo, vval, exp.test.exp.getType(), exp.test.itestopt, !exp.test.itestopt.isnot);
                const eexp = `${ttest} ? (${bbn} = ${bexptrue}, ${texp}) : (${bbn} = ${bexpfalse}, ${fexp})`;
                return !toplevel ? `(${eexp})` : eexp;
            }
        }
    }

    emitExpression(exp: Expression, toplevel: boolean): string {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression: {
                return this.emitLiteralNoneExpression();
            }
            case ExpressionTag.LiteralBoolExpression: {
                return this.emitLiteralBoolExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralNatExpression: {
                return this.emitLiteralNatExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralIntExpression: {
                return this.emitLiteralIntExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralBigNatExpression: {
                return this.emitLiteralBigNatExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralBigIntExpression: {
                return this.emitLiteralBigIntExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralRationalExpression: {
                return this.emitLiteralRationalExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralFloatExpression: {
                return this.emitLiteralFloatExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDecimalExpression: {
                return this.emitLiteralDecimalExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDecimalDegreeExpression: {
                return this.emitLiteralDecimalDegreeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralLatLongCoordinateExpression: {
                return this.emitLiteralLatLongCoordinateExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralComplexNumberExpression: {
                return this.emitLiteralComplexNumberExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralByteBufferExpression: {
                return this.emitLiteralByteBufferExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUUIDv4Expression: {
                return this.emitLiteralUUIDv4Expression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUUIDv7Expression: {
                return this.emitLiteralUUIDv7Expression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralSHAContentHashExpression: {
                return this.emitLiteralSHAContentHashExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTZDateTimeExpression: {
                return this.emitLiteralTZDateTimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTAITimeExpression: {
                return this.emitLiteralTAITimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPlainDateExpression: {
                return this.emitLiteralPlainDateExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPlainTimeExpression: {
                return this.emitLiteralPlainTimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralLogicalTimeExpression: {
                return this.emitLiteralLogicalTimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralISOTimeStampExpression: {
                return this.emitLiteralISOTimeStampExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaDateTimeExpression: {
                return this.emitLiteralDeltaDateTimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaISOTimeStampExpression: {
                return this.emitLiteralDeltaISOTimeStampExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaSecondsExpression: {
                return this.emitLiteralDeltaSecondsExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaLogicalExpression: {
                return this.emitLiteralDeltaLogicalExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUnicodeRegexExpression: {
                return this.emitLiteralUnicodeRegexExpression(exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralCRegexExpression: {
                return this.emitLiteralCRegexExpression(exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralCCharExpression: {
                return this.emitLiteralCCharExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUnicodeCharExpression: {
                return this.emitLiteralUnicodeCharExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralStringExpression: {
                return this.emitLiteralStringExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralCStringExpression: {
                return this.emitLiteralCStringExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTypeDeclValueExpression: {
                return this.emitLiteralTypeDeclValueExpression(exp as LiteralTypeDeclValueExpression, toplevel);
            }
            case ExpressionTag.HasEnvValueExpression: {
                return this.emitHasEnvValueExpression(exp as AccessEnvValueExpression);
            }
            case ExpressionTag.AccessEnvValueExpression: {
                return this.emitAccessEnvValueExpression(exp as AccessEnvValueExpression);
            }
            case ExpressionTag.TaskAccessInfoExpression: {
                return this.emitTaskAccessInfoExpression(exp as TaskAccessInfoExpression);
            }
            case ExpressionTag.AccessNamespaceConstantExpression: {
                return this.emitAccessNamespaceConstantExpression(exp as AccessNamespaceConstantExpression);
            }
            case ExpressionTag.AccessStaticFieldExpression: {
                return this.emitAccessStaticFieldExpression(exp as AccessStaticFieldExpression);
            }
            case ExpressionTag.AccessEnumExpression: {
                return this.emitAccessEnumExpression(exp as AccessEnumExpression);
            }
            case ExpressionTag.AccessVariableExpression: {
                return this.emitAccessVariableExpression(exp as AccessVariableExpression);
            }
            case ExpressionTag.ConstructorPrimaryExpression: {
                return this.emitConstructorPrimaryExpression(exp as ConstructorPrimaryExpression, toplevel);
            }
            case ExpressionTag.ConstructorEListExpression: {
                return this.emitConstructorEListExpression(exp as ConstructorEListExpression);
            }
            case ExpressionTag.ConstructorLambdaExpression: {
                return this.emitConstructorLambdaExpression(exp as ConstructorLambdaExpression);
            }
            case ExpressionTag.LetExpression: {
                return this.emitLetExpression(exp as LetExpression);
            }
            case ExpressionTag.LambdaInvokeExpression: {
                return this.emitLambdaInvokeExpression(exp as LambdaInvokeExpression);
            }
            case ExpressionTag.SpecialConstructorExpression: {
                return this.emitSpecialConstructorExpression(exp as SpecialConstructorExpression, toplevel);
            }
            case ExpressionTag.CallNamespaceFunctionExpression: {
                return this.emitCallNamespaceFunctionExpression(exp as CallNamespaceFunctionExpression);
            }
            case ExpressionTag.CallTypeFunctionExpression: {
                return this.emitCallTypeFunctionExpression(exp as CallTypeFunctionExpression);
            }
            case ExpressionTag.LogicActionAndExpression: {
                return this.emitLogicActionAndExpression(exp as LogicActionAndExpression);
            }
            case ExpressionTag.LogicActionOrExpression: {
                return this.emitLogicActionOrExpression(exp as LogicActionOrExpression);
            }
            case ExpressionTag.ParseAsTypeExpression: {
                return this.emitParseAsTypeExpression(exp as ParseAsTypeExpression, toplevel);
            }
            case ExpressionTag.SafeConvertExpression: {
                return this.emitSafeConvertExpression(exp as SafeConvertExpression, toplevel);
            }
            case ExpressionTag.CreateDirectExpression: {
                return this.emitCreateDirectExpression(exp as CreateDirectExpression, toplevel);
            }
            case ExpressionTag.PostfixOpExpression: {
                return this.emitPostfixOp(exp as PostfixOp, toplevel);
            }
            case ExpressionTag.PrefixNotOpExpression: {
                return this.emitPrefixNotOpExpression(exp as PrefixNotOpExpression, toplevel);
            }
            case ExpressionTag.PrefixNegateOrPlusOpExpression: {
                return this.emitPrefixNegateOrPlusOpExpression(exp as PrefixNegateOrPlusOpExpression, toplevel);
            }
            case ExpressionTag.BinAddExpression: {
                return this.emitBinAddExpression(exp as BinAddExpression, toplevel);
            }
            case ExpressionTag.BinSubExpression: {
                return this.emitBinSubExpression(exp as BinSubExpression, toplevel);
            }
            case ExpressionTag.BinMultExpression: {
                return this.emitBinMultExpression(exp as BinMultExpression, toplevel);
            }
            case ExpressionTag.BinDivExpression: {
                return this.emitBinDivExpression(exp as BinDivExpression, toplevel);
            }
            case ExpressionTag.BinKeyEqExpression: {
                return this.emitBinKeyEqExpression(exp as BinKeyEqExpression, toplevel);
            }
            case ExpressionTag.BinKeyNeqExpression: {
                return this.emitBinKeyNeqExpression(exp as BinKeyNeqExpression, toplevel);
            }
            case ExpressionTag.KeyCompareEqExpression: {
                return this.emitKeyCompareEqExpression(exp as KeyCompareEqExpression, toplevel);
            }
            case ExpressionTag.KeyCompareLessExpression: {
                return this.emitKeyCompareLessExpression(exp as KeyCompareLessExpression, toplevel);
            }
            case ExpressionTag.NumericEqExpression: {
                return this.emitNumericEqExpression(exp as NumericEqExpression, toplevel);
            }
            case ExpressionTag.NumericNeqExpression: {
                return this.emitNumericNeqExpression(exp as NumericNeqExpression, toplevel);
            }
            case ExpressionTag.NumericLessExpression: {
                return this.emitNumericLessExpression(exp as NumericLessExpression, toplevel);
            }
            case ExpressionTag.NumericLessEqExpression: {
                return this.emitNumericLessEqExpression(exp as NumericLessEqExpression, toplevel);
            }
            case ExpressionTag.NumericGreaterExpression: {
                return this.emitNumericGreaterExpression(exp as NumericGreaterExpression, toplevel);
            }
            case ExpressionTag.NumericGreaterEqExpression: {
                return this.emitNumericGreaterEqExpression(exp as NumericGreaterEqExpression, toplevel);
            }
            case ExpressionTag.BinLogicAndExpression: {
                return this.emitBinLogicAndExpression(exp as BinLogicAndExpression, toplevel);
            }
            case ExpressionTag.BinLogicOrExpression: {
                return this.emitBinLogicOrExpression(exp as BinLogicOrExpression, toplevel);
            }
            case ExpressionTag.BinLogicImpliesExpression: {
                return this.emitBinLogicImpliesExpression(exp as BinLogicImpliesExpression, toplevel);
            }
            case ExpressionTag.BinLogicIFFExpression: {
                return this.emitBinLogicIFFExpression(exp as BinLogicIFFExpression, toplevel);
            }
            case ExpressionTag.MapEntryConstructorExpression: {
                return this.emitMapEntryConstructorExpression(exp as MapEntryConstructorExpression);
            }
            case ExpressionTag.IfExpression: {
                return this.emitIfExpression(exp as IfExpression, toplevel);
            }
            default: {
                assert(exp.tag === ExpressionTag.ErrorExpression, "Unknown expression kind");
                return "[ERROR EXPRESSION]";
            }
        }
    }

    private emitCallRefInvokeExpression(exp: CallRefInvokeExpression): string {
        const rcvrval = this.emitExpression(exp.rcvr, false);

        const rtrgt = (this.tproc(exp.resolvedTrgt as TypeSignature) as NominalTypeSignature);
        const mdecl = rtrgt.decl.methods.find((m) => m.name === exp.name) as MethodDecl;

        const argl: string[] = [];
        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            const ii = exp.shuffleinfo[i];
            if(ii[0] === -1) {
                argl.push("undefined");
            }
            else {
                const aaexp = this.emitExpression(exp.args.args[ii[0]].exp, true);
                argl.push(aaexp);
            }
        }

        if(exp.restinfo !== undefined) {
            const restl: ArgumentValue[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                const rri = exp.restinfo[i];
                if(!rri[1]) {
                    restl.push(exp.args.args[rri[0]]);
                }
                else {
                    assert(false, "Not implemented -- CallPostfixInvoken -- spread into rest");
                }
            }

            const rtype = exp.resttype as NominalTypeSignature;
            if(rtype.decl instanceof ListTypeDecl) {
                argl.push(this.processEmitListConstructor(rtype.alltermargs[0], restl));
            }
            else {
                assert(false, "Not implemented -- CallPostfixInvoken -- rest");
            }
        }

        if(EmitNameManager.isMethodCallObjectRepr(rtrgt)) {
            if(exp.terms.length === 0) {
                return `${rcvrval}.${EmitNameManager.generateAccssorNameForMethodImplicit(this.getCurrentNamespace(), rtrgt, mdecl, exp.terms.map((tt) => this.tproc(tt)))}(${argl.join(", ")})`;
            }
            else {
                return `${rcvrval}.$scall("${exp.name}", "${EmitNameManager.generateTermKeyFromTermTypes(exp.terms.map((tt) => this.tproc(tt)))}"${argl.length !== 0 ? ", " : ""}${argl.join(", ")})`; 
            }
        }
        else {
            return `${EmitNameManager.generateAccssorNameForMethodFull(this.getCurrentNamespace(), rtrgt, mdecl, exp.terms.map((tt) => this.tproc(tt)))}.call(${rcvrval}${argl.length !== 0 ? ", " : ""}${argl.join(", ")})`;
        }
    }

    private emitCallRefVariableExpression(exp: CallRefVariableExpression): string {
        return this.emitCallRefInvokeExpression(exp);
    }

    private emitCallRefThisExpression(exp: CallRefThisExpression): string {
        return this.emitCallRefInvokeExpression(exp);
    }

    private emitCallRefSelfExpression(exp: CallRefSelfExpression): string {
        assert(false, "Not implemented -- CallRefSelf");
    }
    
    private emitCallTaskActionExpression(exp: CallTaskActionExpression): string {
        assert(false, "Not implemented -- CallTaskAction");
    }

    private emitTaskRunExpression(exp: TaskRunExpression): string {
        assert(false, "Not implemented -- TaskRun");
    }

    private emitTaskMultiExpression(exp: TaskMultiExpression): string {
        assert(false, "Not implemented -- TaskMulti");
    }

    private emitTaskDashExpression(exp: TaskDashExpression): string {
        assert(false, "Not implemented -- TaskDash");
    }
    
    private emitTaskAllExpression(exp: TaskAllExpression): string {
        assert(false, "Not implemented -- TaskAll");
    }
    
    private emitTaskRaceExpression(exp: TaskRaceExpression): string {
        assert(false, "Not implemented -- TaskRace");
    }

    //TODO: late update this to return 2 strings -- first the sequence to compute the RHS (incl ref updates and early exits) then the actual value expression
    private emitExpressionRHS(exp: Expression): string {
        const ttag = exp.tag;

        let estr = "";
        switch (ttag) {
            case ExpressionTag.CallRefVariableExpression: {
                estr = this.emitCallRefVariableExpression(exp as CallRefVariableExpression);
                break;
            }
            case ExpressionTag.CallRefThisExpression: {
                estr = this.emitCallRefThisExpression(exp as CallRefThisExpression);
                break;
            }
            case ExpressionTag.CallRefSelfExpression: {
                estr = this.emitCallRefSelfExpression(exp as CallRefSelfExpression);
                break;
            }
            case ExpressionTag.CallTaskActionExpression: {
                estr = this.emitCallTaskActionExpression(exp as CallTaskActionExpression);
                break;
            }
            case ExpressionTag.TaskRunExpression: {
                estr = this.emitTaskRunExpression(exp as TaskRunExpression);
                break;
            }
            case ExpressionTag.TaskMultiExpression: {
                estr = this.emitTaskMultiExpression(exp as TaskMultiExpression);
                break;
            }
            case ExpressionTag.TaskDashExpression: {
                estr = this.emitTaskDashExpression(exp as TaskDashExpression);
                break;
            }
            case ExpressionTag.TaskAllExpression: {
                estr = this.emitTaskAllExpression(exp as TaskAllExpression);
                break;
            }
            case ExpressionTag.TaskRaceExpression: {
                estr = this.emitTaskRaceExpression(exp as TaskRaceExpression);
                break;
            }
            default: {
                if(ttag === ExpressionTag.CallNamespaceFunctionExpression) {
                    estr = this.emitCallNamespaceFunctionExpression(exp as CallNamespaceFunctionExpression);
                }
                else if(ttag === ExpressionTag.CallTypeFunctionExpression) {
                    estr = this.emitCallTypeFunctionExpression(exp as CallTypeFunctionExpression);
                }
                else if(ttag === ExpressionTag.LambdaInvokeExpression) {
                    estr = this.emitLambdaInvokeExpression(exp as LambdaInvokeExpression);
                }
                else if(ttag === ExpressionTag.PostfixOpExpression) {
                    estr = this.emitPostfixOp(exp as PostfixOp, true);
                }
                else {
                    estr = this.emitExpression(exp, true);
                }

                break;
            }
        }

        let opstr = "";
        switch (ttag) {
            case ExpressionTag.CallRefVariableExpression:
            case ExpressionTag.CallRefThisExpression:
            case ExpressionTag.CallRefSelfExpression: {
                const vv = this.emitAccessVariableExpression((exp as CallRefInvokeExpression).rcvr);
                opstr = `(_$rv = ${estr}, ${vv} = _$rv.ref, _$rv.return)`;
                break;
            }
            default: {
                let vvopt: RefArgumentValue | undefined = undefined;

                if(ttag === ExpressionTag.CallNamespaceFunctionExpression) {
                    vvopt = (exp as CallNamespaceFunctionExpression).args.args.find((arg) => arg instanceof RefArgumentValue);
                }
                else if(ttag === ExpressionTag.CallTypeFunctionExpression) {
                    vvopt = (exp as CallTypeFunctionExpression).args.args.find((arg) => arg instanceof RefArgumentValue);
                }
                else if(ttag === ExpressionTag.LambdaInvokeExpression) {
                    vvopt = (exp as LambdaInvokeExpression).args.args.find((arg) => arg instanceof RefArgumentValue);
                }
                else if(ttag === ExpressionTag.PostfixOpExpression) {
                    const pop = exp as PostfixOp;
                    const lop = pop.ops[pop.ops.length - 1];
                    vvopt = (lop instanceof PostfixInvoke) ? lop.args.args.find((arg) => arg instanceof RefArgumentValue) : undefined;
                }
                else {
                    ;
                }

                if(vvopt === undefined) {
                    opstr = estr;
                }
                else {
                    const vv = this.emitAccessVariableExpression((vvopt.exp as AccessVariableExpression));
                    opstr = `(_$rv = ${estr}, ${vv} = _$rv.ref, _$rv.return)`;
                }

                break;
            }
        }

        return opstr;
    }

    private emitEmptyStatement(stmt: EmptyStatement): string {
        return ";";
    }
    
    private emitVariableDeclarationStatement(stmt: VariableDeclarationStatement): string {
        return `let ${stmt.name};`;
    }
    
    private emitVariableMultiDeclarationStatement(stmt: VariableMultiDeclarationStatement): string {
        return `let ${stmt.decls.map((dd) => dd.name).join(", ")};`;
    }
    
    private emitVariableInitializationStatement(stmt: VariableInitializationStatement): string {
        const rhsexp = this.emitExpressionRHS(stmt.exp);
        
        if(stmt.name === "_") {
            return `${rhsexp};`;
        }
        else {
            return `${stmt.isConst ? "const": "let"} ${stmt.name} = ${rhsexp};`;
        }
    }
    
    private emitVariableMultiInitializationStatement(stmt: VariableMultiInitializationStatement): string {
        if(!Array.isArray(stmt.exp)) {
            const eexp = this.emitExpressionRHS(stmt.exp);
            const idecls = stmt.decls.map((dd) => dd.name === "_" ? " " : dd.name);

            return `${stmt.isConst ? "const": "let"} [${idecls.join(", ")}] = ${eexp};`;
        }
        else {
            //TODO: need to check if there are deps between the defs and uses in the expressions here!!!
            
            const eexps = stmt.exp.map((ee) => this.emitExpression(ee, true));
            const idecls = stmt.decls.map((dd, ii) => `${dd.name} = ${eexps[ii]}`);

            return `${stmt.isConst ? "const": "let"} ${idecls.join(", ")};`;

        }
    }

    private emitVariableAssignmentStatement(stmt: VariableAssignmentStatement): string {
        const rhsexp = this.emitExpressionRHS(stmt.exp);

        if(stmt.name === "_") {
            return `${rhsexp};`;
        }
        else {
            return `${stmt.name} = ${rhsexp};`;
        }
    }

    private emitVariableMultiAssignmentStatement(stmt: VariableMultiAssignmentStatement): string {
        if(!Array.isArray(stmt.exp)) {
            const eexp = this.emitExpressionRHS(stmt.exp);
            const names = stmt.names.map((nn) => nn === "_" ? " " : nn);

            return `[${names.join(", ")}] = ${eexp};`;
        }
        else {
            const eexps = stmt.exp.map((ee) => this.emitExpression(ee, true));

            return `${stmt.names.map((nn, ii) => `${nn} = ${eexps[ii]}`).join(", ")};`;            
        }
    }

    private emitVariableRetypeStatement(stmt: VariableRetypeStatement): string {
        assert("Not Implemented -- emitVariableRetypeStatement");

        //TODO: add type check assertion
        return "";
    }

    private emitReturnVoidStatement(stmt: ReturnVoidStatement): string {
        assert(this.optrefreturn !== undefined);

        if(this.returncompletecall === undefined) {
            return `return {return: null, ref: ${this.optrefreturn}};`;
        }
        else {
            return `return {return: ${this.returncompletecall}, ref: ${this.optrefreturn} };`;
        }
    }

    private emitReturnSingleStatement(stmt: ReturnSingleStatement): string {
        const rexp = this.emitExpressionRHS(stmt.value);

        if(this.returncompletecall === undefined) {
            if(this.optrefreturn === undefined) {
                return `return ${rexp};`;
            }
            else {
                return `return {return: ${rexp}, ref: ${this.optrefreturn}};`;
            }
        }
        else {
            if(this.optrefreturn === undefined) {
                return `return ${this.returncompletecall.replace("$[RESULT ARG]$", rexp)};`;
            }
            else {
                return `return {return: ${this.returncompletecall.replace("$[RESULT ARG]$", rexp)}, ref: ${this.optrefreturn}};`;
            }
        }
    }

    private emitReturnMultiStatement(stmt: ReturnMultiStatement): string {
        const rexp = `[${stmt.value.map((vv) => this.emitExpression(vv, true)).join(", ")}]`;

        if(this.returncompletecall === undefined) {
            if(this.optrefreturn === undefined) {
                return `return ${rexp};`;
            }
            else {
                return `return {return: ${rexp}, ref: ${this.optrefreturn}];`;
            }
        }
        else {
            if(this.optrefreturn === undefined) {
                return `return ${this.returncompletecall.replace("$[RESULT ARG]$", rexp)};`;
            }
            else {
                return `return {return: ${this.returncompletecall.replace("$[RESULT ARG]$", rexp)}, ref: ${this.optrefreturn}};`;
            }
        }
    }

    private emitIfStatement(stmt: IfStatement, fmt: JSCodeFormatter): string {
        if(stmt.cond.itestopt === undefined) {
            let test = this.emitExpression(stmt.cond.exp, true);
            if(this.tproc(stmt.cond.exp.getType()).tkeystr !== "Bool") {
                test = `_$bval${test}`;
            }

            const body = this.emitBlockStatement(stmt.trueBlock, fmt);
            return `if(${test}) ${body}`;
        }
        else {
            if(stmt.binder === undefined) {
                const test = this.processITestAsTest(this.emitExpression(stmt.cond.exp, true), stmt.cond.exp.getType(), stmt.cond.itestopt);
                const body = this.emitBlockStatement(stmt.trueBlock, fmt);
                return `if(${test}) ${body}`;
            }
            else {
                const vexp = this.emitExpression(stmt.cond.exp, false);
                const test = this.processITestAsTest(vexp, stmt.cond.exp.getType(), stmt.cond.itestopt);
                const bexp = this.processITestAsConvert(stmt.sinfo, vexp, stmt.cond.exp.getType(), stmt.cond.itestopt, stmt.cond.itestopt.isnot);

                fmt.indentPush();
                const body = this.emitBlockStatement(stmt.trueBlock, fmt);
                const bassign = fmt.indent(`let ${stmt.binder.srcname} = ${bexp};`) + " " + body + fmt.nl();
                fmt.indentPop();

                return `if(${test}) {${fmt.nl()}${bassign}${fmt.indent("}")}`;
            }
        }
    }

    private emitIfElseStatement(stmt: IfElseStatement, fmt: JSCodeFormatter): string {
        if(stmt.cond.itestopt === undefined) {
            let test = this.emitExpression(stmt.cond.exp, true);
            if(this.tproc(stmt.cond.exp.getType()).tkeystr !== "Bool") {
                test = `_$bval${test}`;
            }

            const tbody = this.emitBlockStatement(stmt.trueBlock, fmt);
            const fbody = this.emitBlockStatement(stmt.falseBlock, fmt);

            return `if(${test}) ${tbody}${fmt.nl()}${fmt.indent("")}else ${fbody}`;
        }
        else {
            if(stmt.binder === undefined) {
                const test = this.processITestAsTest(this.emitExpression(stmt.cond.exp, true), stmt.cond.exp.getType(), stmt.cond.itestopt);
                const tbody = this.emitBlockStatement(stmt.trueBlock, fmt);
                const fbody = this.emitBlockStatement(stmt.falseBlock, fmt);

                return `if(${test}) ${tbody}${fmt.nl()}${fmt.indent("")}else ${fbody}`;
            }
            else {
                const vexp = this.emitExpression(stmt.cond.exp, false);
                const test = this.processITestAsTest(vexp, stmt.cond.exp.getType(), stmt.cond.itestopt);

                const btrue = this.processITestAsConvert(stmt.sinfo, vexp, stmt.cond.exp.getType(), stmt.cond.itestopt, stmt.cond.itestopt.isnot);
                const bfalse = this.processITestAsConvert(stmt.sinfo, vexp, stmt.cond.exp.getType(), stmt.cond.itestopt, !stmt.cond.itestopt.isnot);

                fmt.indentPush();
                const tbody = this.emitBlockStatement(stmt.trueBlock, fmt);
                const tbassign = fmt.indent(`let ${stmt.binder.srcname} = ${btrue};`) + " " + tbody + fmt.nl();

                const fbody = this.emitBlockStatement(stmt.falseBlock, fmt);
                const fbassign = fmt.indent(`let ${stmt.binder.srcname} = ${bfalse};`) + " " + fbody + fmt.nl();
                fmt.indentPop();

                return `if(${test}) {${fmt.nl()}${tbassign}${fmt.indent("}")}${fmt.nl()}${fmt.indent("else {")}${fmt.nl()}${fbassign}${fmt.indent("}")}`;
            }
        }
    }

    private emitIfElifElseStatement(stmt: IfElifElseStatement, fmt: JSCodeFormatter): string {  
        const cffops = stmt.condflow.map((elif, ii) => {
            const kww = ii === 0 ? "if" : fmt.indent("else if");
            const test = this.emitExpression(elif.cond, true);
            const body = this.emitBlockStatement(elif.block, fmt);

            return `${kww}(${test}) ${body}${fmt.nl()}`
        });

        const eeop = this.emitBlockStatement(stmt.elseflow, fmt);

        return cffops.join("") + fmt.indent("else ") + eeop;
    }

    private emitSwitchStatement(stmt: SwitchStatement, fmt: JSCodeFormatter): string {
        const val = this.emitExpression(stmt.sval, true);
        const ecases = stmt.switchflow.slice(0, -1).map((cc, ii) => {
            const cval = this.emitExpression((cc.lval as LiteralExpressionValue).exp, true);
            const cbody = this.emitBlockStatement(cc.value, fmt);

            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(stmt.optypes[ii]));
            return (ii !== 0 ? fmt.indent("else ") : "") + `if (_$fkeq.${optype}(${val}, ${cval})) ${cbody}`;
        });

        const finalop = stmt.switchflow[stmt.switchflow.length - 1];
        let elseval: string = "";
        if(stmt.mustExhaustive) {
            elseval = fmt.indent(`else ${this.emitBlockStatement(finalop.value, fmt)}`);
        }
        else {
            fmt.indentPush();
            const relseval = fmt.indent(this.emitBlockStatement(finalop.value, fmt));
            const cval = this.emitExpression((finalop.lval as LiteralExpressionValue).exp, true);

            const optype = EmitNameManager.generateFunctionLookupKeyForOperators(this.tproc(stmt.optypes[stmt.switchflow.length - 1]));
            const chkstmt = fmt.indent(`_$exhaustive(_$fkeq.${optype}(${val}, ${cval}), ${this.getErrorInfo("exhaustive switch", stmt.sinfo, undefined)});`);
            fmt.indentPop();

            elseval = fmt.indent(`else {${fmt.nl()}${chkstmt}${fmt.nl()}${relseval}${fmt.nl()}${fmt.indent("}")}`);
        }

        return [...ecases, elseval].join(fmt.nl());
    }

    private emitMatchCase(mtype: TypeSignature, value: BlockStatement, vval: string, vtype: TypeSignature, binderinfo: BinderInfo | undefined, fmt: JSCodeFormatter): [string, string] {
        const tmtype = this.tproc(mtype) as TypeSignature;
        const tvtype = this.tproc(vtype) as TypeSignature;
        
        const ttest = `(${this.emitITestAsTest_Type(vval, tvtype, tmtype, false)})`;
        
        if(binderinfo === undefined) {
            return [ttest, this.emitBlockStatement(value, fmt)];
        }
        else {
            fmt.indentPush();
            const blck = this.emitBlockStatement(value, fmt);
            fmt.indentPop();

            return [ttest, `{ let ${binderinfo.srcname} = ${vval}; ${blck}${fmt.nl()}${fmt.indent("}")}`];
        }
    }

    private emitMatchStatement(stmt: MatchStatement, fmt: JSCodeFormatter): string {
        const val = this.emitExpression(stmt.sval[0], true);
        const ecases = stmt.matchflow.slice(0, -1).map((cc, ii) => {
            const ccase = this.emitMatchCase(cc.mtype as TypeSignature, cc.value, val, stmt.sval[0].getType(), stmt.sval[1], fmt);
            return (ii !== 0 ? fmt.indent("else if ") : "if ") + ccase[0] + " " + ccase[1];
        });

        const finalop = stmt.matchflow[stmt.matchflow.length - 1];    
        let elseval: string = "";
        if(stmt.mustExhaustive) {
            const ccase = this.emitMatchCase((finalop.mtype || stmt.implicitFinalType) as TypeSignature, finalop.value, val, stmt.sval[0].getType(), stmt.sval[1], fmt);
            elseval = fmt.indent(`else ${ccase[1]}`);
        }
        else {
            
            fmt.indentPush();
            const ccase = this.emitMatchCase((finalop.mtype || stmt.implicitFinalType) as TypeSignature, finalop.value, val, stmt.sval[0].getType(), stmt.sval[1], fmt);
            const chkstmt = fmt.indent(`_$exhaustive(${ccase[0]}, ${this.getErrorInfo("exhaustive switch", stmt.sinfo, undefined)});`);
            const bbody = fmt.indent(ccase[1]);
            fmt.indentPop();

            elseval = fmt.indent(`else {${fmt.nl()}${chkstmt}${fmt.nl()}${bbody}${fmt.nl()}${fmt.indent("}")}`);
        }

        return [...ecases, elseval].join(fmt.nl());
    }

    private emitAbortStatement(stmt: AbortStatement): string {
        return `_$abort(${this.getErrorInfo("abort", stmt.sinfo, undefined)});`;
    }

    private emitAssertStatement(stmt: AssertStatement): string {
        if(!isBuildLevelEnabled(stmt.level, this.buildlevel)) {
            return ";";
        }
        else {
            return `_$assert(${this.emitExpression(stmt.cond, true)}, ${this.getErrorInfo(stmt.cond.emit(true, new CodeFormatter()), stmt.sinfo, undefined)});`;
        }
    }

    private emitValidateStatement(stmt: ValidateStatement): string {
        return `_$validate(${this.emitExpression(stmt.cond, true)}, ${this.getErrorInfo(stmt.cond.emit(true, new CodeFormatter()), stmt.sinfo, stmt.diagnosticTag)});`;
    }

    private emitDebugStatement(stmt: DebugStatement): string {
        const eexp = this.emitExpression(stmt.value, true);
        const emittype = this.tproc(stmt.value.getType()).tkeystr;
        const eebsqon = `_$emitBSQON("${emittype}", ${eexp})`;
        return `try { console.log("_debug>> " + ${eebsqon}); } catch { console.log("Error evaluating debug statement @ ${this.currentfile}:${stmt.sinfo.line}"); }`;
    }

    private emitVoidRefCallStatement(stmt: VoidRefCallStatement): string {
        return this.emitExpressionRHS(stmt.exp) + ";";
    }

    private emitUpdateStatement(stmt: UpdateStatement): string {
        const vexp = this.emitExpression(stmt.vexp, true);
        const updatecalls = stmt.updates.map((upd) => upd[0] + `: (($${upd[0]}) => { return ` + this.emitExpression(upd[1], true) + `; })(${vexp}.${upd[0]})`).join(", ");

        return `${vexp} = ${vexp}.$update({ ${updatecalls} });`;
    }

    private emitVarUpdateStatement(stmt: VarUpdateStatement): string {
        return this.emitUpdateStatement(stmt);
    }

    private emitThisUpdateStatement(stmt: ThisUpdateStatement): string {
        return this.emitUpdateStatement(stmt);
    }

    private emitSelfUpdateStatement(stmt: SelfUpdateStatement): string {
        assert(false, "Not implemented -- SelfUpdate");
    }

    private emitEnvironmentUpdateStatement(stmt: EnvironmentUpdateStatement): string {
        assert(false, "Not implemented -- EnvironmentUpdate");
    }

    private emitEnvironmentBracketStatement(stmt: EnvironmentBracketStatement): string {
        assert(false, "Not implemented -- EnvironmentBracket");
    }

    private emitTaskStatusStatement(stmt: TaskStatusStatement): string {
        assert(false, "Not implemented -- TaskStatus");
    }

    private emitTaskEventEmitStatement(stmt: TaskEventEmitStatement): string {
        assert(false, "Not implemented -- TaskEventEmit");
    }

    private emitTaskYieldStatement(stmt: TaskYieldStatement): string {
        assert(false, "Not implemented -- TaskYield");
    }

    private emitStatementArray(stmts: Statement[], fmt: JSCodeFormatter): string[] {
        let stmtstrs: string[] = [];

        fmt.indentPush();
        let prevskip = true;
        for(let i = 0; i < stmts.length; ++i) {
            const stmti = stmts[i];
            const sstr = fmt.indent(this.emitStatement(stmti, fmt));

            if(i === stmts.length - 1) {
                stmtstrs.push(sstr);
                stmtstrs.push(fmt.nl());
            }
            else {
                const stag = stmti.tag;
                switch(stag) {
                    case StatementTag.BlockStatement: {
                        if(!prevskip) {
                            stmtstrs.push(fmt.nl());
                        }
                        stmtstrs.push(sstr);
                        stmtstrs.push(fmt.nl());
                        prevskip = true;
                        break;
                    }
                    case StatementTag.IfStatement:
                    case StatementTag.IfElseStatement: 
                    case StatementTag.IfElifElseStatement:
                    case StatementTag.SwitchStatement:
                    case StatementTag.MatchStatement: {
                        if(!prevskip) {
                            stmtstrs.push(fmt.nl());
                        }
                        stmtstrs.push(sstr);
                        stmtstrs.push(fmt.nl());
                        prevskip = true;
                        break;
                    }
                    default: {
                        stmtstrs.push(sstr);
                        prevskip = false;
                    }
                }
                stmtstrs.push(fmt.nl());
            }
        }
        fmt.indentPop();

        return stmtstrs;
    }

    private emitBlockStatement(stmt: BlockStatement, fmt: JSCodeFormatter): string {
        const stmts = this.emitStatementArray(stmt.statements, fmt);

        return ["{", fmt.nl(), ...stmts, fmt.indent("}")].join("");
    }

    private emitStatement(stmt: Statement, fmt: JSCodeFormatter): string {
        switch(stmt.tag) {
            case StatementTag.EmptyStatement: {
                return this.emitEmptyStatement(stmt as EmptyStatement);
            }
            case StatementTag.VariableDeclarationStatement: {
                return this.emitVariableDeclarationStatement(stmt as VariableDeclarationStatement);
            }
            case StatementTag.VariableMultiDeclarationStatement: {
                return this.emitVariableMultiDeclarationStatement(stmt as VariableMultiDeclarationStatement);
            }
            case StatementTag.VariableInitializationStatement: {
                return this.emitVariableInitializationStatement(stmt as VariableInitializationStatement);
            }
            case StatementTag.VariableMultiInitializationStatement: {
                return this.emitVariableMultiInitializationStatement(stmt as VariableMultiInitializationStatement);
            }
            case StatementTag.VariableAssignmentStatement: {
                return this.emitVariableAssignmentStatement(stmt as VariableAssignmentStatement);
            }
            case StatementTag.VariableMultiAssignmentStatement: {
                return this.emitVariableMultiAssignmentStatement(stmt as VariableMultiAssignmentStatement);
            }
            case StatementTag.VariableRetypeStatement: {
                return this.emitVariableRetypeStatement(stmt as VariableRetypeStatement);
            }
            case StatementTag.ReturnVoidStatement: {
                return this.emitReturnVoidStatement(stmt as ReturnVoidStatement);
            }
            case StatementTag.ReturnSingleStatement: {
                return this.emitReturnSingleStatement(stmt as ReturnSingleStatement);
            }
            case StatementTag.ReturnMultiStatement: {
                return this.emitReturnMultiStatement(stmt as ReturnMultiStatement);
            }
            case StatementTag.IfStatement: {
                return this.emitIfStatement(stmt as IfStatement, fmt);
            }
            case StatementTag.IfElseStatement: {
                return this.emitIfElseStatement(stmt as IfElseStatement, fmt);
            }
            case StatementTag.IfElifElseStatement: {
                return this.emitIfElifElseStatement(stmt as IfElifElseStatement, fmt);
            }
            case StatementTag.SwitchStatement: {
                return this.emitSwitchStatement(stmt as SwitchStatement, fmt);
            }
            case StatementTag.MatchStatement: {
                return this.emitMatchStatement(stmt as MatchStatement, fmt);
            }
            case StatementTag.AbortStatement: {
                return this.emitAbortStatement(stmt as AbortStatement);
            }
            case StatementTag.AssertStatement: {
                return this.emitAssertStatement(stmt as AssertStatement);
            }
            case StatementTag.ValidateStatement: {
                return this.emitValidateStatement(stmt as ValidateStatement);
            }
            case StatementTag.DebugStatement: {
                return this.emitDebugStatement(stmt as DebugStatement);
            }
            case StatementTag.VoidRefCallStatement: {
                return this.emitVoidRefCallStatement(stmt as VoidRefCallStatement);
            }
            case StatementTag.VarUpdateStatement: {
                return this.emitVarUpdateStatement(stmt as VarUpdateStatement);
            }
            case StatementTag.ThisUpdateStatement: {
                return this.emitThisUpdateStatement(stmt as ThisUpdateStatement);
            }
            case StatementTag.SelfUpdateStatement: {
                return this.emitSelfUpdateStatement(stmt as SelfUpdateStatement);
            }
            case StatementTag.EnvironmentUpdateStatement: {
                return this.emitEnvironmentUpdateStatement(stmt as EnvironmentUpdateStatement);
            }
            case StatementTag.EnvironmentBracketStatement: {
                return this.emitEnvironmentBracketStatement(stmt as EnvironmentBracketStatement);
            }
            case StatementTag.TaskStatusStatement: {
                return this.emitTaskStatusStatement(stmt as TaskStatusStatement);
            }
            case StatementTag.TaskEventEmitStatement: {
                return this.emitTaskEventEmitStatement(stmt as TaskEventEmitStatement);
            }
            case StatementTag.TaskYieldStatement: {
                return this.emitTaskYieldStatement(stmt as TaskYieldStatement);
            }
            case StatementTag.BlockStatement: {
                return this.emitBlockStatement(stmt as BlockStatement, fmt);
            }
            default: {
                assert(stmt.tag === StatementTag.ErrorStatement, `Unknown statement kind -- ${stmt.tag}`);

                return "[ERROR STATEMENT]";
            }
        }
    }

    private emitBuiltinBodyImplementation(body: BuiltinBodyImplementation, fmt: JSCodeFormatter): string {
        const bname = body.builtin;

        var preop: string = "";
        var bop: string = "";
        if(bname === "s_nat_to_cstring") {
            bop = `v.toString()`;
        }
        else if(bname === "s_nat_from_cstring") {
            bop = `BigInt(str)`;
        }
        else if(bname === "s_int_to_cstring") {
            bop = `v.toString()`;
        }
        else if(bname === "s_int_from_cstring") {
            bop = `BigInt(str)`;
        }
        else if(bname === "s_float_power") {
            bop = `Math.pow(a, b)`;
        }
        else if(bname === "s_float_sqrt") {
            bop = `Math.sqrt(a)`;
        }
        else if(bname === "cstring_empty") {
            bop = `s === ""`;
        }
        else if(bname === "cstring_size") {
            bop = `BigInt(s.length)`;
        }
        else if(bname === "cstring_starts_with_string") {
            bop = `s.startsWith(prefix)`;
        }
        else if(bname === "cstring_ends_with_string") {
            bop = `s.endsWith(suffix)`;
        }
        else if(bname === "cstring_contains_string") {
            bop = `s.includes(find)`;
        }
        else if(bname === "cstring_contains_string_unique") {
            bop = `[...s.matchAll(target)].length === 1`
        }
        else if(bname === "cstring_append") {
            bop = `s + c`;
        }
        else if(bname === "cstring_prepend") {
            bop = `c + s`;
        }
        else if(bname === "cstring_concat2") {
            bop = `s1 + s2`;
        }
        else if(bname === "cstring_remove_prefix_string") {
            bop = `s.slice(prefix.length)`;
        }
        else if(bname === "cstring_remove_suffix_string") {
            bop = `s.slice(0, s.length - suffix.length)`;
        }
        else if(bname === "cstring_replace_unique_string_occurrence") {
            bop = `s.replace(target, replacement)`;
        }
        else if(bname === "cstring_replace_all_string_occurrences") {
            bop = `s.replaceAll(target, replacement)`;
        }
        else if(bname === "string_from_cstring") {
            bop = `s`;
        }
        else if(bname === "string_empty") {
            bop = `s === ""`;
        }
        else if(bname === "string_starts_with_string") {
            bop = `s.startsWith(prefix)`;
        }
        else if(bname === "string_ends_with_string") {
            bop = `s.endsWith(suffix)`;
        }
        else if(bname === "string_contains_string") {
            bop = `s.includes(find)`;
        }
        else if(bname === "string_contains_string_unique") {
            bop = `[...s.matchAll(target)].length === 1`
        }
        else if(bname === "string_append") {
            bop = `s + c`;
        }
        else if(bname === "string_prepend") {
            bop = `c + s`;
        }
        else if(bname === "string_concat2") {
            bop = `s1 + s2`;
        }
        else if(bname === "string_remove_prefix_string") {
            bop = `s.slice(prefix.length)`;
        }
        else if(bname === "string_remove_suffix_string") {
            bop = `s.slice(0, s.length - suffix.length)`;
        }
        else if(bname === "string_replace_unique_string_occurrence") {
            bop = `s.replace(target, replacement)`;
        }
        else if(bname === "string_replace_all_string_occurrences") {
            bop = `s.replaceAll(target, replacement)`;
        }
        else if(bname === "s_algo_while") {
            preop = `var state = s; while(guard(state)) { state = op(state); } `;
            bop = `state`;
        }
        else {
            assert(false, `Unknown builtin function -- ${bname}`);
        }

        return `{ ${preop}return ${bop}; }`;
    }

    private emitBodyImplementation(body: BodyImplementation, ismethod: boolean, initializers: string[], preconds: string[], refsaves: string[], optrefreturn: string | undefined, returncompletecall: string | undefined, fmt: JSCodeFormatter): string | undefined {
        if(body instanceof AbstractBodyImplementation || body instanceof PredicateUFBodyImplementation) {
            return undefined;
        }

        if(body instanceof SynthesisBodyImplementation) {
            assert(false, "Not implemented -- emitSynthesisBodyImplementation");
        }
        else if(body instanceof BuiltinBodyImplementation) {
            return this.emitBuiltinBodyImplementation(body, fmt);
        }
        else {
            let stmts: string[] = [];
            if(body instanceof ExpressionBodyImplementation) {
                if(optrefreturn === undefined) {
                    stmts.push(`return ${this.emitExpression(body.exp, true)};`);
                }
                else {
                    stmts.push(`return {return: ${this.emitExpression(body.exp, true)}, ref: ${optrefreturn}};`);
                }
            }
            else {
                assert(body instanceof StandardBodyImplementation);
                
                const origOptRef = this.optrefreturn;
                const origCompleteCall = this.returncompletecall;

                this.optrefreturn = optrefreturn;
                this.returncompletecall = returncompletecall;

                stmts = this.emitStatementArray(body.statements, fmt);

                this.optrefreturn = origOptRef;
                this.returncompletecall = origCompleteCall;
            }

            let renames: string[] = [];
            if(ismethod) {
                fmt.indentPush();
                renames = [fmt.indent("let $this$ = this;")]
                fmt.indentPop();
            }

            if(this.bindernames.size !== 0) {
                fmt.indentPush();
                const bvars = fmt.indent(`var ${[...this.bindernames].join(", ")};${fmt.nl(2)}`);
                fmt.indentPop();

                stmts = [bvars, ...stmts];
            }
            this.bindernames.clear();

            if(initializers.length === 0 && preconds.length === 0 && refsaves.length === 0) {
                const renamesstr = renames.join(fmt.nl());
                return ["{", fmt.nl(), renamesstr, (renames.length !== 0 ? fmt.nl() : ""), ...stmts, fmt.indent("}")].join("");
            }
            else {
                fmt.indentPush();
                fmt.indentPush()
                const ideclops = initializers.map((ii) => fmt.indent(ii)).join(fmt.nl());
                fmt.indentPop()
                const ideclstr = initializers.length !== 0 ? `${fmt.indent("{")}${fmt.nl()}${ideclops}${fmt.nl()}${fmt.indent("}\n")}` : "";

                const renamesstr = renames.join(fmt.nl());
                const precondstr = preconds.map((ii) => fmt.indent(ii)).join(fmt.nl());
                const refsavestr = refsaves.map((ii) => fmt.indent(ii)).join(fmt.nl());
                fmt.indentPop();

                return ["{", fmt.nl(), ideclstr, (initializers.length !== 0 ? fmt.nl(2) : ""), renamesstr, (renames.length !== 0 ? fmt.nl() : ""), precondstr, (preconds.length !== 0 ? fmt.nl(2) : ""), refsavestr, (refsaves.length !== 0 ? fmt.nl(2) : ""), ...stmts, fmt.indent("}")].join("");
            }
        }
    }

    private emitParameterInitializers(params: InvokeParameterDecl[]): string[] {
        //TODO: we need to compute the dependency order here and check for cycles later -- right now just do left to right

        let inits: string[] = [];
        for(let i = 0; i < params.length; ++i) {
            const p = params[i];
            
            if(p.optDefaultValue !== undefined) {
                inits.push(`if(${p.name} === undefined) { $${p.name} = ${p.name} = ${this.emitExpression(p.optDefaultValue.exp, true)}; }`);
            }
        }

        if(inits.length === 0) {
            return [];
        }
        else {
            const iidecl = "let " + params.map((p) => `$${p.name} = ${p.name}`).join(", ") + ";";
            return [iidecl, ...inits];
        }
    }

    private emitRequires(requires: PreConditionDecl[]): string[] {
        let preconds: string[] = [];
        for(let i = 0; i < requires.length; ++i) {
            const precond = requires[i];
            if(isBuildLevelEnabled(precond.level, this.buildlevel)) {
                const eexp = this.emitExpression(precond.exp, true);
                if(precond.issoft) {
                    preconds.push(`_$softprecond(${eexp}, ${this.getErrorInfo(precond.exp.emit(true, new CodeFormatter()), precond.sinfo, precond.diagnosticTag)});`);
                }
                else {
                    preconds.push(`_$precond(${eexp}, ${this.getErrorInfo(precond.exp.emit(true, new CodeFormatter()), precond.sinfo, precond.diagnosticTag)});`);
                }
            }
        }

        return preconds;
    }

    private emitRefSaves(params: InvokeParameterDecl[]): string[] {
        let refsaves: string[] = [];
        for(let i = 0; i < params.length; ++i) {
            const p = params[i];
            if(p.isRefParam) {
                refsaves.push(`$${p.name} = ${p.name}`);
            }
        }

        return refsaves;
    }

    private emitEnsures(ensures: PostConditionDecl[]): string[] {
        let postconds: string[] = [];
        for(let i = 0; i < ensures.length; ++i) {
            const postcond = ensures[i];
            if(isBuildLevelEnabled(postcond.level, this.buildlevel)) {
                const eexp = this.emitExpression(postcond.exp, true);
                if(postcond.issoft) {
                    postconds.push(`_$softpostcond(${eexp}, ${this.getErrorInfo(postcond.exp.emit(true, new CodeFormatter()), postcond.sinfo, postcond.diagnosticTag)});`);
                }
                else {
                    postconds.push(`_$postcond(${eexp}, ${this.getErrorInfo(postcond.exp.emit(true, new CodeFormatter()), postcond.sinfo, postcond.diagnosticTag)});`);
                }
            }
        }

        return postconds;
    }

    private emitInvariants(rcvr: NominalTypeSignature, bnames: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[], invariants: InvariantDecl[]): string[] {
        let invexps: string[] = [];
        for(let i = 0; i < invariants.length; ++i) {
            const inv = invariants[i];

            if(isBuildLevelEnabled(inv.level, this.buildlevel)) {
                const chkcall = `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`;
                const args = (rcvr.decl instanceof TypedeclTypeDecl) ? "$value" : bnames.map((fi) => "$" + fi.name).join(", ");
                const body = this.emitExpression(inv.exp.exp, true);

                invexps.push(`${chkcall}: { value: (${args}) => ${body} }`);
            }
        }

        return invexps;
    }

    private emitValidates(rcvr: NominalTypeSignature, bnames: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[], validates: ValidateDecl[]): string[] {
        let vexps: string[] = [];
        for(let i = 0; i < validates.length; ++i) {
            const inv = validates[i];

            const chkcall = `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`;
            const args = (rcvr.decl instanceof TypedeclTypeDecl) ? "$value" : bnames.map((fi) => "$" + fi.name).join(", ");
            const body = this.emitExpression(inv.exp.exp, true);

            vexps.push(`${chkcall}: { value: (${args}) => ${body} }`);
        }

        return vexps;
    }

    private emitExplicitInvokeFunctionDeclSignature(idecl: FunctionInvokeDecl): string {
        return `(${idecl.params.map((p) => p.name).join(", ")})`;
    }

    private checkExplicitFunctionInvokeDeclMetaData(idecl: FunctionInvokeDecl, inits: string[], preconds: string[], refsaves: string[]): string[] {
        inits.push(...this.emitParameterInitializers(idecl.params));
        preconds.push(...this.emitRequires(idecl.preconditions));

        const ensurescc = this.emitEnsures(idecl.postconditions);
        if(ensurescc.length !== 0) {
            refsaves.push(...this.emitRefSaves(idecl.params));
        }

        return ensurescc;
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

    private emitTestCallForFunctionDecl(fdecl: NamespaceFunctionDecl) {
        if(!this.testEmitEnabled(fdecl)) {
            return undefined;
        }

        if(this.testgroups.find((gg) => gg[0] === fdecl.file) === undefined) {
            this.testgroups.push([fdecl.file, []]);
        }
        let tarray = (this.testgroups.find((gg) => gg[0] === fdecl.file) as [string, string[]])[1];
    
        const invname = EmitNameManager.generateAccssorNameForNamespaceTestFunction(this.getCurrentNamespace(), fdecl);
        
        //TODO: we will need to handle test functions with parameters here
        assert(fdecl.params.length === 0, "Not implemented -- fuzzing for test functions with parameters");

        let invop = "";
        const testmsg = `process.stdout.write("    Test @${fdecl.sinfo.line} -- ${fdecl.name}... ");`;
        if(fdecl.fkind === "chktest") {
            invop = `${testmsg} _$ccount++; try { const result = ${invname}(); if(result) { _$passcount++; process.stdout.write("pass " + _$ccount.toString() + "/" + _$totalcount.toString() + "\\n"); } else { _$failcount++; process.stdout.write("fail " + _$ccount.toString() + "/" + _$totalcount.toString() + "\\n"); } } catch { _$errorcount++; process.stdout.write("error "  + _$ccount.toString() + "/" + _$totalcount.toString() + "\\n"); }`;
        }
        else {
            invop = `${testmsg} _$ccount++; try { ${invname}(); _$passcount++; process.stdout.write("pass " + _$ccount.toString() + "/" + _$totalcount.toString() + "\\n"); } catch { _$errorcount++; process.stdout.write("error "  + _$ccount.toString() + "/" + _$totalcount.toString() + "\\n"); }`;
        }

        tarray.push(invop);
    }

    private emitFunctionDecl(fdecl: FunctionInvokeDecl, optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined] | undefined, optmapping: TemplateNameMapper | undefined, fmt: JSCodeFormatter): {body: string, resfimpl: string | undefined} {
        const omap = this.mapper;
        if(optmapping !== undefined) {
            this.mapper = TemplateNameMapper.tryMerge(optenclosingtype !== undefined ? optenclosingtype[1] : undefined, optmapping);
        }

        const sig = this.emitExplicitInvokeFunctionDeclSignature(fdecl);

        let initializers: string[] = [];
        let preconds: string[] = [];
        let refsaves: string[] = [];
        const ensures = this.checkExplicitFunctionInvokeDeclMetaData(fdecl, initializers, preconds, refsaves);

        let resf: string | undefined = undefined;
        let resfimpl: string | undefined = undefined;
        if(ensures.length !== 0) {
            //TODO: we will need to handle ref params here too
            assert(fdecl.params.every((p) => !p.isRefParam), "Not implemented -- checkEnsuresRefParams");

            const resb = [...ensures.map((e) => fmt.indent(e)), fmt.indent("return $return;")].join(fmt.nl());

            let [resf, rss] = fdecl instanceof NamespaceFunctionDecl ? EmitNameManager.generateOnCompleteDeclarationNameForNamespaceFunction(this.getCurrentNamespace(), fdecl as NamespaceFunctionDecl, optmapping) : [EmitNameManager.generateOnCompleteDeclarationNameForTypeFunction(fdecl as TypeFunctionDecl, optmapping), true];
            const decl = `(${fdecl.params.map((p) => p.name).join(", ")}, $return)${rss ? " => " : " "}{${fmt.nl()}${resb}${fmt.nl()}${fmt.indent("}")}`;
            if(fdecl instanceof NamespaceFunctionDecl || optmapping !== undefined) {
                resfimpl = `${resf}${decl}`;
            }
            else {
                resfimpl = `${resf} { value: ${decl} }`;
            }
        }

        const optrefv = fdecl.params.find((p) => p.isRefParam);
        const body = this.emitBodyImplementation(fdecl.body, false, initializers, preconds, refsaves, optrefv !== undefined ? optrefv.name : undefined, resf, fmt);
        this.mapper = omap;

        const [nf, nss] = fdecl instanceof NamespaceFunctionDecl ? EmitNameManager.generateDeclarationNameForNamespaceFunction(this.getCurrentNamespace(), fdecl as NamespaceFunctionDecl, optmapping) : [EmitNameManager.generateDeclarationNameForTypeFunction(fdecl as TypeFunctionDecl, optmapping), true];
        const decl = `${sig}${nss ? " => " : " "}${body}`;
        let bdecl: string;
        if(fdecl instanceof NamespaceFunctionDecl || optmapping !== undefined) {
            bdecl = `${nf}${decl}`;
        }
        else {
            bdecl = `${nf} { value: ${decl} }`;
        }
        
        if(fdecl instanceof NamespaceFunctionDecl) {
            if(fdecl.fkind === "errtest" || fdecl.fkind === "chktest" || fdecl.fkind === "example") {
                this.emitTestCallForFunctionDecl(fdecl);
            }
        }

        return {body: bdecl, resfimpl: resfimpl};
    }

    private emitFunctionDecls(optenclosingtype: [NominalTypeSignature, TemplateNameMapper | undefined] | undefined, fdecls: [FunctionInvokeDecl, FunctionInstantiationInfo | undefined][], fmt: JSCodeFormatter): string[] {
        let decls: string[] = [];
        let tests: string[] = [];

        for(let i = 0; i < fdecls.length; ++i) {
            const fdecl = fdecls[i][0];
            const fii = fdecls[i][1]; 
    
            this.currentfile = fdecl.file;

            if(fii !== undefined) {
                if(fii.binds === undefined) {
                    const {body, resfimpl} = this.emitFunctionDecl(fdecl, optenclosingtype, undefined, fmt);
            
                    if(resfimpl !== undefined) {
                        decls.push(resfimpl);
                    }
                    decls.push(body);
                
                    tests.push(...tests);
                }
                else {
                    fmt.indentPush();
                    let idecls: string[] = []
                    for(let j = 0; j < fii.binds.length; ++j) {
                        const {body, resfimpl} = this.emitFunctionDecl(fdecl, optenclosingtype, fii.binds[j], fmt);
            
                        if(resfimpl !== undefined) {
                            idecls.push(fmt.indent(resfimpl));
                        }
                        idecls.push(fmt.indent(body));

                        tests.push(...tests);
                    }
                    fmt.indentPop();

                    if(fdecl instanceof NamespaceFunctionDecl) {
                        if(this.getCurrentNamespace().isTopNamespace()) {
                            const fobj = `export const ${fdecl.name} = {${fmt.nl()}${idecls.map((dd) => dd).join("," + fmt.nl())}${fmt.nl()}${fmt.indent("}")}`;
                            decls.push(fobj);
                        }
                        else {
                            const fobj = `${fdecl.name}: {${fmt.nl()}${idecls.map((dd) => dd).join("," + fmt.nl())}${fmt.nl()}${fmt.indent("}")}`;
                            decls.push(fobj);
                        }
                    }
                    else {
                        const fobj = `${fdecl.name}: { value: {${fmt.nl()}${idecls.map((dd) => dd).join("," + fmt.nl())}${fmt.nl()}${fmt.indent("}")} }`;
                        decls.push(fobj);                      
                    }
                }
            }
        }

        return decls;
    }

    private emitExplicitMethodDeclSignature(idecl: MethodDecl): string {
        return `(${idecl.params.map((p) => p.name).join(", ")})`;
    }

    private checkExplicitMethodDeclMetaData(rcvrtype: NominalTypeSignature, idecl: MethodDecl, inits: string[], preconds: string[], refsaves: string[]): string[] {
        inits.push(...this.emitParameterInitializers(idecl.params));
        preconds.push(...this.emitRequires(idecl.preconditions));

        if(idecl.isThisRef) {
            inits.push(`const $this = this;`);
        }

        const ensurescc = this.emitEnsures(idecl.postconditions);
        if(ensurescc.length !== 0) {
            refsaves.push(...this.emitRefSaves(idecl.params));
        }

        return ensurescc;
    }

    private emitMethodDecl(rcvrtype: [NominalTypeSignature, TemplateNameMapper | undefined], mdecl: MethodDecl, optmapping: TemplateNameMapper | undefined, fmt: JSCodeFormatter): {body: string, resfimpl: string | undefined} {
        const omap = this.mapper;
        if(optmapping !== undefined) {
            this.mapper = TemplateNameMapper.tryMerge(rcvrtype[1], optmapping);
        }

        const sig = this.emitExplicitMethodDeclSignature(mdecl);

        let initializers: string[] = [];
        let preconds: string[] = [];
        let refsaves: string[] = [];
        const ensures = this.checkExplicitMethodDeclMetaData(rcvrtype[0], mdecl, initializers, preconds, refsaves);

        let resf: string | undefined = undefined;
        let resfimpl: string | undefined = undefined;
        if(ensures.length !== 0) {
            //TODO: we will need to handle ref params here too
            assert(!mdecl.isThisRef && mdecl.params.every((p) => !p.isRefParam), "Not implemented -- checkEnsuresRefParams");

            const resb = [...ensures.map((e) => fmt.indent(e)), fmt.indent("return $return;")].join(fmt.nl());

            let resf = EmitNameManager.generateOnCompleteDeclarationNameForMethod(rcvrtype[0], mdecl, optmapping);
            const decl = `(${mdecl.params.map((p) => p.name).join(", ")}, $return) => {${fmt.nl()}${resb}${fmt.nl()}${fmt.indent("}")}`;
            if(optmapping !== undefined) {
                resfimpl = `${resf}${decl}`;
            }
            else {
                resfimpl = `${resf} { value: ${decl} }`;
            }
        }

        const optreft = mdecl.isThisRef ? "$this$" : undefined
        const optrefv = mdecl.params.find((p) => p.isRefParam);
        const body = this.emitBodyImplementation(mdecl.body, true, initializers, preconds, refsaves, optreft || (optrefv !== undefined ? optrefv.name : undefined), resf, fmt);
        this.mapper = omap;

        const nf = EmitNameManager.generateDeclarationNameForMethod(rcvrtype[0], mdecl, optmapping);
        const decl = `function${sig} ${body}`;
        let bdecl: string;
        if(optmapping !== undefined) {
            bdecl = `${nf}${decl}`;
        }
        else {
            bdecl = `${nf} { value: ${decl} }`;
        }
        
        return {body: bdecl, resfimpl: resfimpl};
    }

    private emitMethodDecls(rcvr: [NominalTypeSignature, TemplateNameMapper | undefined], mdecls: [MethodDecl, MethodInstantiationInfo | undefined][], fmt: JSCodeFormatter): string[] {
        let decls: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {
            const mdecl = mdecls[i][0];
            const mii = mdecls[i][1];

            this.currentfile = mdecl.file;

            if(mii !== undefined) {
                if(mii.binds === undefined) {
                    const {body, resfimpl} = this.emitMethodDecl(rcvr, mdecl, undefined, fmt);
            
                    if(resfimpl !== undefined) {
                        decls.push(resfimpl);
                    }
                    decls.push(body);
                }
                else {
                    fmt.indentPush();
                    let idecls: string[] = []
                    for(let j = 0; j < mii.binds.length; ++j) {
                        const {body, resfimpl} = this.emitMethodDecl(rcvr, mdecl, mii.binds[j], fmt);
            
                        if(resfimpl !== undefined) {
                            idecls.push(fmt.indent(resfimpl));
                        }
                        idecls.push(fmt.indent(body));
                    }
                    fmt.indentPop();

                    const fobj = `${mdecl.name}: { value: {${fmt.nl()}${idecls.map((dd) => dd).join("," + fmt.nl())}${fmt.nl()}${fmt.indent("}")} }`;
                    decls.push(fobj);
                }
            }
        }

        return decls;
    }
/*
    private emitTaskMethodDecls(rcvr: TypeSignature, mdecls: [TaskMethodDecl, TemplateNameMapper][]): string[] {
        let decls: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {
            assert(false, "Not implemented -- checkTaskMethodDecl");
        }

        return decls;
    }

    private emitTaskActionDecls(rcvr: TypeSignature, mdecls: TaskActionDecl[]): string[] {
        let decls: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {
            assert(false, "Not implemented -- checkTaskActionDecl");
        }

        return decls;
    }
*/

    private emitConstMemberDecls(decls: ConstMemberDecl[]): string[] {
        let cdecls: string[] = [];
        for(let i = 0; i < decls.length; ++i) {
            const m = decls[i];

            const eexp = this.emitExpression(m.value.exp, true);
            
            if(m.value.exp instanceof LiteralNoneExpression || m.value.exp instanceof LiteralSimpleExpression || m.value.exp instanceof LiteralRegexExpression) {
                cdecls.push(`${m.name}: { value: function() { return ${eexp}; } }`);

            }
            else {
                const lexp = `() => ${eexp}`;
                cdecls.push(`${m.name}: { value: function () { return _$memoconstval(this._$consts, "${m.name}", ${lexp}); } }`);
            }
        }

        if(cdecls.length !== 0) {
            cdecls = ["_$consts: { value: {} }", ...cdecls];
        }

        return cdecls;
    }

    private emitMemberFieldInitializers(tdecl: AbstractNominalTypeDecl, decls: MemberFieldDecl[], fmt: JSCodeFormatter): string[] {
        const inits = decls.filter((d) => d.defaultValue !== undefined);

        let initializers: string[] = [];
        for(let i = 0; i < inits.length; ++i) {
            const m = inits[i];
            if(m.defaultValue !== undefined) {
                const chkcall = `$default$${m.name}`;
                const args = tdecl.saturatedBFieldInfo.map((fi) => "$" + fi.name).join(", "); // --------- TODO: we need to compute dependencies and cycles

                const body = this.emitExpression(m.defaultValue.exp, true);
                initializers.push(`${chkcall}: { value: (${args}) => ${body} }`);
            }
        }

        return initializers;
    }

    private static generateRcvrForNominalAndBinds(ntype: AbstractNominalTypeDecl, binds: TemplateNameMapper | undefined, implicitbinds: string[] | undefined): NominalTypeSignature {
        if(binds === undefined) {
            return new NominalTypeSignature(ntype.sinfo, undefined, ntype, []);
        }
        else {
            const tbinds = implicitbinds !== undefined ? implicitbinds.map((bb) => binds.resolveTemplateMapping(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), bb))) : ntype.terms.map((tt) => binds.resolveTemplateMapping(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), tt.name)));
            return new NominalTypeSignature(ntype.sinfo, undefined, ntype, tbinds);
        }
    }

    private emitTypeSymbol(rcvr: NominalTypeSignature): string {
        return `$tsym: { value: Symbol.for("${rcvr.tkeystr}") }`;
    }

    private tryLookupBindsFor(ptype: NominalTypeSignature, mdecl: MethodDecl): MethodInstantiationInfo | undefined {
        const inns = ptype.decl.ns.emit();
        const nsii = this.asminstantiation.find((ai) => ai.ns.emit() === inns);
        if(nsii === undefined) {
            return undefined;
        }

        const tii = nsii.typebinds.get(ptype.decl.name);
        if(tii === undefined) {
            return undefined;
        }

        const btti = tii.find((ii) => ii.tkey === ptype.tkeystr);
        if(btti === undefined) {
            return undefined;
        }

        return btti.methodbinds.get(mdecl.name);
    }

    private emitStaticInherits(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature): string[] {
        let pcalls: string[] = [];

        for(let i = 0; i < tdecl.saturatedProvides.length; ++i) {
            const ptype = this.tproc(tdecl.saturatedProvides[i]) as NominalTypeSignature;

            const smethods = ptype.decl.methods.filter((m) => !m.attributes.some((attr) => attr.name === "override" || attr.name === "virtual" || attr.name === "abstract"));
            for(let j = 0; j < smethods.length; ++j) {
                const mbind = this.tryLookupBindsFor(ptype, smethods[j]);

                if(mbind !== undefined) {
                    if(mbind.binds === undefined) {
                        pcalls.push(`${smethods[j].name}: { value: ${EmitNameManager.generateAccssorNameForMethodFull(this.currentns as NamespaceDeclaration, ptype, smethods[j], [])} }`);
                    }
                    else {
                        assert(false, "Not implemented -- emitStaticInherits");
                    }
                }
            }
        }

        return pcalls;
    }

    private emitVTable(tdecl: AbstractNominalTypeDecl, fmt: JSCodeFormatter): string[] {
        return ["[VTABLE -- NOT IMPLEMENTED]"];
    }

    private emitStaticInvokeFunction(): string {
        return `$scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }`;
    }

    private emitDefaultFieldInitializers(ffinfo: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[]): string[] {
        //TODO: we need to compute the dependency order here and check for cycles later -- right now just do left to right

        let inits: string[] = [];
        for(let i = 0; i < ffinfo.length; ++i) {
            const f = ffinfo[i];
            
            if(f.hasdefault) {
                const aargs = ffinfo.map((fi) => `$${fi.name}`).join(", ");
                const icall = `${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(f.containingtype) as NominalTypeSignature, `$default$${f.name}`)}(${aargs})`;
                inits.push(`if(${f.name} === undefined) { $${f.name} = ${f.name} = ${icall}; }`);
            }
        }

        if(inits.length === 0) {
            return [];
        }
        else {
            const iidecl = "let " + ffinfo.map((f) => `$${f.name} = ${f.name}`).join(", ") + ";";
            return [iidecl, ...inits];
        }
    }

    private generateObjectCreationExp(ffinfo: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[], rcvr: NominalTypeSignature): string {
        const paramargs = ffinfo.map((fi) => `${fi.name}: { value: ${fi.name}, enumerable: true }`).join(", ");
        const protoref = EmitNameManager.generateAccessorForTypeConstructorProto(this.currentns as NamespaceDeclaration, rcvr);

        return `return Object.create(${protoref}, { ${paramargs} });`;
    }

    private emitCreate(tdecl: AbstractNominalTypeDecl, ffinfo: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[] | undefined, rcvr: NominalTypeSignature, fmt: JSCodeFormatter): string {
        const ddecls = ffinfo === undefined ? this.emitDefaultFieldInitializers(tdecl.saturatedBFieldInfo) : [];

        let rechks: string[] = [];
        if(tdecl instanceof TypedeclTypeDecl && tdecl.optofexp !== undefined) {
            if(tdecl.optofexp.exp.tag === ExpressionTag.LiteralUnicodeRegexExpression) {
                rechks.push(`_$formatchk(_$accepts(${this.emitLiteralUnicodeRegexExpression(tdecl.optofexp.exp as LiteralRegexExpression)}, value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex", tdecl.optofexp.exp.sinfo, undefined)});`);
            }
            else if(tdecl.optofexp.exp.tag === ExpressionTag.LiteralCRegexExpression) {
                rechks.push(`_$formatchk(_$accepts(${this.emitLiteralCRegexExpression(tdecl.optofexp.exp as LiteralRegexExpression)}, value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex", tdecl.optofexp.exp.sinfo, undefined)});`);
            }
            else {
                const nsaccess = this.emitAccessNamespaceConstantExpression(tdecl.optofexp.exp as AccessNamespaceConstantExpression);
                const retag = `'${(tdecl.optofexp.exp as AccessNamespaceConstantExpression).ns.ns.join("::")}::${(tdecl.optofexp.exp as AccessNamespaceConstantExpression).name}'`;
                rechks.push(`_$formatchk(_$accepts(${nsaccess}, value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex -- " + (tdecl.optofexp.exp as AccessNamespaceConstantExpression).name, tdecl.optofexp.exp.sinfo, retag)});`);
            }
        }

        const cchks = tdecl.allInvariants.map((inv) => {
            const chkcall = `${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(inv.containingtype) as NominalTypeSignature, `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`)}`;
            const args = (ffinfo || inv.containingtype.decl.saturatedBFieldInfo).map((fi) => fi.name).join(", ");
            const info = this.getErrorInfo("failed invariant", inv.sinfo, inv.tag);

            return `_$invariant(${chkcall}(${args}), ${info});`
        });

        const ccons =  this.generateObjectCreationExp(ffinfo || tdecl.saturatedBFieldInfo, rcvr);

        fmt.indentPush();
        const bbody = [...ddecls, ...rechks, ...cchks, ccons].map((ee) => fmt.indent(ee)).join(fmt.nl());
        fmt.indentPop();

        return `$create: { value: (${(ffinfo || tdecl.saturatedBFieldInfo).map((fi) => fi.name).join(", ")}) => {${fmt.nl()}${bbody}${fmt.nl()}${fmt.indent("}")} }`;
    }

    private emitUpdate(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature, fmt: JSCodeFormatter): string {
        const cchks = tdecl.allInvariants.map((inv) => {
            const chkcall = `${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(inv.containingtype) as NominalTypeSignature, `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`)}`;
            const args = inv.containingtype.decl.saturatedBFieldInfo.map((fi) => "vobj." + fi.name).join(", ");
            const info = this.getErrorInfo("failed invariant", inv.sinfo, inv.tag);

            return `_$invariant(${chkcall}(${args}), ${info});`
        });

        const protoref = EmitNameManager.generateAccessorForTypeConstructorProto(this.currentns as NamespaceDeclaration, rcvr);
        const ccons = "let vobj = {...this, ...updates};"
        const updop = `return Object.assign(Object.create(${protoref}), vobj);`;

        fmt.indentPush();
        const bbody = [ccons, ...cchks, updop].map((ee) => fmt.indent(ee)).join(fmt.nl());
        fmt.indentPop();

        return `$update: { value: function(updates) {${fmt.nl()}${bbody}${fmt.nl()}${fmt.indent("}")} }`;
    }

    private emitCreateAPIValidate(tdecl: AbstractNominalTypeDecl, ffinfo: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[] | undefined, rcvr: NominalTypeSignature, fmt: JSCodeFormatter): string {
        const ddecls = ffinfo === undefined ? this.emitDefaultFieldInitializers(tdecl.saturatedBFieldInfo) : [];

        let rechks: string[] = [];
        if(tdecl instanceof TypedeclTypeDecl && tdecl.optofexp !== undefined) {
            if(tdecl.optofexp.exp.tag === ExpressionTag.LiteralUnicodeRegexExpression) {
                rechks.push(`_$formatchk(_$accepts(${this.emitLiteralUnicodeRegexExpression(tdecl.optofexp.exp as LiteralRegexExpression)}, value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex", tdecl.optofexp.exp.sinfo, undefined)});`);
            }
            else if(tdecl.optofexp.exp.tag === ExpressionTag.LiteralCRegexExpression) {
                rechks.push(`_$formatchk(_$accepts(${this.emitLiteralCRegexExpression(tdecl.optofexp.exp as LiteralRegexExpression)}, value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex", tdecl.optofexp.exp.sinfo, undefined)});`);
            }
            else {
                const nsaccess = this.emitAccessNamespaceConstantExpression(tdecl.optofexp.exp as AccessNamespaceConstantExpression);
                const retag = `'${(tdecl.optofexp.exp as AccessNamespaceConstantExpression).ns.ns.join("::")}::${(tdecl.optofexp.exp as AccessNamespaceConstantExpression).name}'`;
                rechks.push(`_$formatchk(_$accepts(${nsaccess}, value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex -- " + (tdecl.optofexp.exp as AccessNamespaceConstantExpression).name, tdecl.optofexp.exp.sinfo, retag)});`);
            }
        }

        const cchks = tdecl.allInvariants.map((inv) => {
            const chkcall = `${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(inv.containingtype) as NominalTypeSignature, `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`)}`;
            const args = (ffinfo || inv.containingtype.decl.saturatedBFieldInfo).map((fi) => fi.name).join(", ");
            const info = this.getErrorInfo("failed invariant", inv.sinfo, inv.tag);

            return `_$invariant(${chkcall}(${args}), ${info});`
        });

        const vchks = tdecl.allValidates.map((inv) => {
            const chkcall = `${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(inv.containingtype) as NominalTypeSignature, `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`)}`;
            const args = (ffinfo || inv.containingtype.decl.saturatedBFieldInfo).map((fi) => fi.name).join(", ");
            const info = this.getErrorInfo("failed validation", inv.sinfo, inv.tag);

            return `_$validate(${chkcall}(${args}), ${info});`
        });

        const ccons =  this.generateObjectCreationExp(ffinfo || tdecl.saturatedBFieldInfo, rcvr);

        fmt.indentPush();``
        const bbody = [...ddecls, ...rechks, ...cchks, ...vchks, ccons].map((ee) => fmt.indent(ee)).join(fmt.nl());
        fmt.indentPop();

        return `$createAPI: { value: (${(ffinfo || tdecl.saturatedBFieldInfo).map((fi) => fi.name).join(", ")}) => {${fmt.nl()}${bbody}${fmt.nl()}${fmt.indent("}")} }`;
    }

    private emitBSQONParseAPI(tdecl: AbstractNominalTypeDecl, usesvalidate: boolean, ffinfo: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[] | undefined, rcvr: NominalTypeSignature, specialop: string | undefined, fmt: JSCodeFormatter): string {
        const createcall = EmitNameManager.generateAccessorForConstructorParseAPI(this.currentns as NamespaceDeclaration, rcvr, usesvalidate);
        const dfields = ffinfo === undefined ? tdecl.saturatedBFieldInfo : ffinfo;
        
        let body: string;
        if(dfields.length === 0) {
            body = `{ return ${createcall}(); }`;
        }
        else if(dfields.length === 1) {
            const sdf = dfields[0];
            const fi = `${specialop !== undefined}, "${sdf.name}", "${sdf.type.tkeystr}"`;

            let chekcall: string;
            if(specialop !== undefined) {
                chekcall = `parser.checkSpecialCons("${specialop}")`;
            }
            else {
                chekcall = `parser.checkConsType("${rcvr.tkeystr}")`;
            }

            if(!sdf.hasdefault) {
                body = `{ ${chekcall}; return ${createcall}(parser.parseSingleArg(${fi})); }`;
            }
            else {
                body = `{ ${chekcall}; return ${createcall}(parser.parseSingleOrDefaultArg(${fi})); }`;               
            }
        }
        else {
            const parray = "[" + dfields.map((fi) => { return `["${fi.name}", "${fi.type.tkeystr}"]`; }) + "]";

            body = `{ parser.checkConsType("${rcvr.tkeystr}"); const vals = parser.parseArgListGeneral(${parray}); return ${createcall}(...vals); }`;
        }

        return `$parseAPI: { value: (parser) => ${body} }`;
    }

    private emitBSQONEmitAPI(tdecl: AbstractNominalTypeDecl, ffinfo: {name: string, type: TypeSignature, hasdefault: boolean, containingtype: NominalTypeSignature}[] | undefined, rcvr: NominalTypeSignature, fmt: JSCodeFormatter): string {
        const dfields = ffinfo === undefined ? tdecl.saturatedBFieldInfo : ffinfo;
        
        let body: string;
        if(dfields.length === 0) {
            body = `{ return "${rcvr.tkeystr}{}"; }`;
        }
        else if(dfields.length === 1) {
            const sdf = dfields[0];
            const evv = `emitter.emitValue("${sdf.type.tkeystr}", value.${sdf.name})`;
            body = `{ return "${rcvr.tkeystr}{" + ${evv} + "}"; }`;
        }
        else {
            const emits = dfields.map((fi) => { return `emitter.emitValue("${fi.type.tkeystr}", value.${fi.name})`; }).join(' + ", " + ');
            body = `{ return "${rcvr.tkeystr}{" + ${emits} + "}"; }`;
        }

        return `$emitAPI: { value: (emitter, value) => ${body} }`;
    }

    private emitStdTypeDeclHelper(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature, optfdecls: MemberFieldDecl[], instantiation: TypeInstantiationInfo, isentity: boolean, fmt: JSCodeFormatter): string[] {
        if(tdecl.terms.length !== 0) {
            this.mapper = instantiation.binds;
        }

        fmt.indentPush();
        let decls: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        const hasoptFields = optfdecls.some((ff) => ff.defaultValue !== undefined);
        if(hasoptFields) {
            decls.push(...this.emitMemberFieldInitializers(tdecl, optfdecls, fmt));
        }

        //make sure all of the invariants on this typecheck
        decls.push(...this.emitInvariants(rcvr, tdecl.saturatedBFieldInfo, tdecl.invariants));
        decls.push(...this.emitValidates(rcvr, tdecl.saturatedBFieldInfo, tdecl.validates));
        
        if(isentity) {
            decls.push(this.emitCreate(tdecl, undefined, rcvr, fmt));
            decls.push(this.emitUpdate(tdecl, rcvr, fmt));

            const usesvalidate = hasoptFields || tdecl.allInvariants.length !== 0 || tdecl.allValidates.length !== 0;
            if(usesvalidate) {
                decls.push(this.emitCreateAPIValidate(tdecl, undefined, rcvr, fmt));
            }

            const islistopscore = tdecl.ns.ns.join("::") === "Core::ListOps";
            const ismapopscore = tdecl.ns.ns.join("::") === "Core::MapOps";

            if(islistopscore && tdecl.name === "BBLeaf") {
                decls.push(`$emitAPI: { value: (emitter, value) => { return ""; } }`);
            }
            else if(islistopscore && tdecl.name === "Leaf") {
                decls.push(`$emitAPI: { value: (emitter, value) => { return emitter.emitValue("${rcvr.alltermargs[0].tkeystr}", value.v); } }`);
            }
            else if(islistopscore && tdecl.name === "Node") {
                const tval = tdecl.saturatedProvides.find((pp) => (pp as NominalTypeSignature).decl.name === "Tree") as NominalTypeSignature;
                const ttype = new NominalTypeSignature(rcvr.sinfo, undefined, tval.decl, rcvr.alltermargs);

                decls.push(`$emitAPI: { value: (emitter, value) => { return [emitter.emitValue("${ttype.tkeystr}", value.l), emitter.emitValue("${ttype.tkeystr}", value.r)].filter((vv) => vv !== "").join(", "); } }`);
            }
            else if(ismapopscore && tdecl.name === "BBLeaf") {
                decls.push(`$emitAPI: { value: (emitter, value) => { return ""; } }`);
            }
            else if(ismapopscore && tdecl.name === "Leaf") {
                const tval = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "MapEntry") as AbstractNominalTypeDecl;
                const ttype = new NominalTypeSignature(rcvr.sinfo, undefined, tval, rcvr.alltermargs);

                decls.push(`$emitAPI: { value: (emitter, value) => { return emitter.emitValue("${ttype}", value.v); } }`);
            }
            else if(ismapopscore && tdecl.name === "Node") {
                const tval = tdecl.saturatedProvides.find((pp) => (pp as NominalTypeSignature).decl.name === "Tree") as NominalTypeSignature;
                const ttype = new NominalTypeSignature(rcvr.sinfo, undefined, tval.decl, rcvr.alltermargs);

                decls.push(`$emitAPI: { value: (emitter, value) => { return [emitter.emitValue("${ttype.tkeystr}", value.l), emitter.emitValue("${ttype.tkeystr}", value.r)].filter((vv) => vv !== "").join(", "); } }`);
            }
            else {
                decls.push(this.emitBSQONParseAPI(tdecl, usesvalidate, undefined, rcvr, undefined, fmt));
                decls.push(this.emitBSQONEmitAPI(tdecl, undefined, rcvr, fmt));
            }
        }

        decls.push(...this.emitConstMemberDecls(tdecl.consts));

        const fdecls = this.emitFunctionDecls([rcvr, instantiation.binds], tdecl.functions.map((fd) => [fd, instantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls);

        const mdecls = this.emitMethodDecls([rcvr, instantiation.binds], tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls);

        if(isentity) {
            decls.push(...this.emitStaticInherits(tdecl, rcvr));
            decls.push(this.emitStaticInvokeFunction());

            if(tdecl.hasDynamicInvokes) {
                decls.push(...this.emitVTable(tdecl, fmt));
            }
        }

        this.mapper = undefined;
        fmt.indentPop();

        return decls;
    }

    private emitInteralSimpleTypeDeclHelper(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter, ifields: {fname: string, ftype: TypeSignature}[] | undefined, specialop: string | undefined, defaultpe: boolean, extradecls: string[], nested: string | undefined): string {
        if(tdecl.terms.length !== 0) {
            this.mapper = instantiation.binds;
        }

        fmt.indentPush();
        let decls: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        if(ifields !== undefined) {
            const iffi = ifields.map((ff) => { return {name: ff.fname, type: ff.ftype, hasdefault: false, containingtype: rcvr}; });
            decls.push(this.emitCreate(tdecl, iffi, rcvr, fmt));

            if(defaultpe) {
                decls.push(this.emitBSQONParseAPI(tdecl, false, iffi, rcvr, specialop, fmt));
                decls.push(this.emitBSQONEmitAPI(tdecl, iffi, rcvr, fmt));
            }
        }

        decls.push(...this.emitConstMemberDecls(tdecl.consts));

        const fdecls = this.emitFunctionDecls([rcvr, instantiation.binds], tdecl.functions.map((fd) => [fd, instantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls);

        const mdecls = this.emitMethodDecls([rcvr, instantiation.binds], tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls);

        if(tdecl instanceof AbstractEntityTypeDecl) {
            decls.push(...this.emitStaticInherits(tdecl, rcvr));
            decls.push(this.emitStaticInvokeFunction());

            if(tdecl.hasDynamicInvokes) {
                decls.push(...this.emitVTable(tdecl, fmt));
            }
        }

        const declsentry = [...decls, ...extradecls].map((dd) => fmt.indent(dd)).join("," + fmt.nl());

        this.mapper = undefined;
        fmt.indentPop();

        const obj = `Object.create(${tdecl instanceof AbstractEntityTypeDecl ? "$VRepr" : "Object.prototype"}, {${fmt.nl()}${declsentry}${fmt.nl()}${fmt.indent("})")}`;

        if(nested !== undefined) {
            return `${tdecl.name}: { value: ${obj} }`;
        }
        else {
            if(tdecl.terms.length !== 0) {
                return `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`;
            }
            else {
                return `export const ${tdecl.name} = ${obj}`;
            }
        }
    }

    private emitPrimitiveEntityTypeDecl(ns: NamespaceDeclaration, tdecl: PrimitiveEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        
        fmt.indentPush();
        let decls: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        decls.push(...this.emitConstMemberDecls(tdecl.consts));

        const fdecls = this.emitFunctionDecls([rcvr, instantiation.binds], tdecl.functions.map((fd) => [fd, instantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls);

        const mdecls = this.emitMethodDecls([rcvr, instantiation.binds], tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls);

        const declsentry = [...decls].map((dd) => fmt.indent(dd)).join("," + fmt.nl());

        this.mapper = undefined;
        fmt.indentPop();

        const obj = `Object.create(Object.prototype, {${fmt.nl()}${declsentry}${fmt.nl()}${fmt.indent("})")}`;

        return `export const ${tdecl.name} = ${obj}`;
    }

    private emitEnumTypeDecl(ns: NamespaceDeclaration, tdecl: EnumTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        fmt.indentPush();
        let decls: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        decls.push("_$memomap: { value: {} }");
        decls.push(...tdecl.members.map((mm, ii) => {
            const paramargs = `value: { value: ${ii}n }`;
            const protoref = EmitNameManager.generateAccessorForTypeConstructorProto(this.currentns as NamespaceDeclaration, rcvr);

            const lexp = `() => Object.create(${protoref}, { ${paramargs} })`;
            return `${mm}: {value: function() { return _$memoconstval(this._$memomap, "${mm}", ${lexp}); } }`;
        }));

        const parselookup = EmitNameManager.generateEnumNameLookupForParse(this.currentns as NamespaceDeclaration, rcvr, "ename");
        const emitgen = "[" + tdecl.members.map((mm) => "mm").join(", ") + "][value.value]";

        decls.push(`$parseAPI: { value: (parser) => { parser.checkConsType("${rcvr.tkeystr}"); const ename = parser.parseEnumNameComponent(); return ${parselookup}; } }`);
        decls.push(`$emitAPI: { value: (emitter, value) => { return "${rcvr.tkeystr}" + "#" + ${emitgen}; } }`);

        const declsentry = [...decls].map((dd) => fmt.indent(dd)).join("," + fmt.nl());

        fmt.indentPop();

        const obj = `Object.create($VRepr, {${fmt.nl()}${declsentry}${fmt.nl()}${fmt.indent("})")}`;

        if(ns.isTopNamespace()) {
            return `export const ${tdecl.name} = ${obj}`;
        }
        else {
            return `${tdecl.name}: ${obj}`;
        }
    }

    private emitTypedeclTypeDecl(ns: NamespaceDeclaration, tdecl: TypedeclTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        fmt.indentPush();
        let decls: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        //make sure all of the invariants on this typecheck
        decls.push(...this.emitInvariants(rcvr, tdecl.saturatedBFieldInfo, tdecl.invariants));
        decls.push(...this.emitValidates(rcvr, tdecl.saturatedBFieldInfo, tdecl.validates));

        decls.push(this.emitCreate(tdecl, [{name: "value", type: this.tproc(tdecl.valuetype), hasdefault: false, containingtype: rcvr}], rcvr, fmt));

        const usesvalidate = tdecl.optofexp !== undefined || tdecl.allInvariants.length !== 0 || tdecl.allValidates.length !== 0;
        if(usesvalidate) {
            decls.push(this.emitCreateAPIValidate(tdecl, [{name: "value", type: this.tproc(tdecl.valuetype), hasdefault: false, containingtype: rcvr}], rcvr, fmt));
        }

        const conscall = EmitNameManager.generateAccessorForConstructorParseAPI(this.currentns as NamespaceDeclaration, rcvr, usesvalidate);
        decls.push(`$parseAPI: { value: (parser) => { const vv = ${conscall}(parser.parseValue("${tdecl.valuetype.tkeystr}")); parser.parseScopedTypeTailing(); return vv; } }`);
        decls.push(`$emitAPI: { value: (emitter, value) => { return emitter.emitValue("${tdecl.valuetype.tkeystr}", value.value) + "<${rcvr.tkeystr}>"; } }`);

        decls.push(...this.emitConstMemberDecls(tdecl.consts));

        const fdecls = this.emitFunctionDecls([rcvr, undefined], tdecl.functions.map((fd) => [fd, instantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls);

        const mdecls = this.emitMethodDecls([rcvr, instantiation.binds], tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls);

        decls.push(...this.emitStaticInherits(tdecl, rcvr));
        decls.push(this.emitStaticInvokeFunction());

        if(tdecl.hasDynamicInvokes) {
            decls.push(...this.emitVTable(tdecl, fmt));
        }

        const declsentry = [...decls].map((dd) => fmt.indent(dd)).join("," + fmt.nl());

        fmt.indentPop();

        const obj = `Object.create($VRepr, {${fmt.nl()}${declsentry}${fmt.nl()}${fmt.indent("})")}`;

        if(ns.isTopNamespace()) {
            return `export const ${tdecl.name} = ${obj}`;
        }
        else {
            return `${tdecl.name}: ${obj}`;
        }
    }

    private emitOkTypeDecl(ns: NamespaceDeclaration, tdecl: OkTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: rcvr.alltermargs[0]}], "ok", true, [], "Result");
    }

    private emitFailTypeDecl(ns: NamespaceDeclaration, tdecl: FailTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "info", ftype: rcvr.alltermargs[1]}], "fail", true, [], "Result");
    }

    private emitAPIRejectedTypeDecl(ns: NamespaceDeclaration, tdecl: APIRejectedTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: rcvr.alltermargs[0]}], undefined, true, [], "APIResult");
    }

    private emitAPIFailedTypeDecl(ns: NamespaceDeclaration, tdecl: APIFailedTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: rcvr.alltermargs[0]}], undefined, true, [], "APIResult");
    }

    private emitAPIErrorTypeDecl(ns: NamespaceDeclaration, tdecl: APIErrorTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: rcvr.alltermargs[0]}], undefined, true, [], "APIResult");
    }

    private emitAPISuccessTypeDecl(ns: NamespaceDeclaration, tdecl: APISuccessTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: rcvr.alltermargs[0]}], undefined, true, [], "APIResult");
    }

    private emitSomeTypeDecl(ns: NamespaceDeclaration, tdecl: SomeTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: rcvr.alltermargs[0]}], "some", true, [], undefined);
    }

    private emitMapEntryTypeDecl(ns: NamespaceDeclaration, tdecl: MapEntryTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);

        const createcall = EmitNameManager.generateAccessorForConstructorParseAPI(this.currentns as NamespaceDeclaration, rcvr, false);
        const pedecls = [
            `$parseAPI: { value: (parser) => { const ee = parser.parseMapEnty("${rcvr.alltermargs[0].tkeystr}", "${rcvr.alltermargs[1].tkeystr}"); return ${createcall}(ee[0], ee[1]); } }`,
            `$emitAPI: { value: (emitter, value) => { return emitter.emitValue("${rcvr.alltermargs[0].tkeystr}", value.key) + " => " + emitter.emitValue("${rcvr.alltermargs[1].tkeystr}", value.value); } }`
        ];

        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "key", ftype: rcvr.alltermargs[0]}, {fname: "value", ftype: rcvr.alltermargs[1]}], undefined, false, pedecls, undefined);
    }

    private emitListTypeDecl(ns: NamespaceDeclaration, tdecl: ListTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);

        const llns = (this.assembly.getCoreNamespace().subns.find((ns) => ns.name === "ListOps") as NamespaceDeclaration);
        const tlva = llns.typedecls.find((tdecl) => tdecl.name === "Tree") as DatatypeTypeDecl;
        const vtype = new NominalTypeSignature(tdecl.sinfo, undefined, tlva, [rcvr.alltermargs[0]]);
        
        const emptyconstdecl = llns.functions.find((ff) => ff.name === "s_list_create_empty") as NamespaceFunctionDecl;
        const pushdecl = llns.functions.find((ff) => ff.name === "s_list_push_back") as NamespaceFunctionDecl;
        const emptyconst = EmitNameManager.generateAccssorNameForNamespaceFunction(this.currentns as NamespaceDeclaration, llns, emptyconstdecl, rcvr.alltermargs) + "()";
        const pushcall = EmitNameManager.generateAccssorNameForNamespaceFunction(this.currentns as NamespaceDeclaration, llns, pushdecl, rcvr.alltermargs);
        const pedecls = [
            `$parseAPI: { value: (parser) => { parser.checkConsType("${rcvr.tkeystr}"); const ee = parser.parseCollectionConsArgs("${rcvr.alltermargs[0].tkeystr}"); return ee.reduce((acc, v) => { return ${pushcall}(acc, v); }, ${emptyconst}); } }`,
            `$emitAPI: { value: (emitter, value) => { return "${rcvr.tkeystr}" + "{" + emitter.emitCollectionEntries("${rcvr.alltermargs[0].tkeystr}", value.value) + "}"; } }`
        ];

        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: vtype}], undefined, false, pedecls, undefined);
    }

    private emitStackTypeDecl(ns: NamespaceDeclaration, tdecl: StackTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined, false, [], undefined);
    }

    private emitQueueTypeDecl(ns: NamespaceDeclaration, tdecl: QueueTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined, false, [], undefined);
    }

    private emitSetTypeDecl(ns: NamespaceDeclaration, tdecl: SetTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined, false, [], undefined);
    }

    private emitMapTypeDecl(ns: NamespaceDeclaration, tdecl: MapTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);

        const mmns = (this.assembly.getCoreNamespace().subns.find((ns) => ns.name === "MapOps") as NamespaceDeclaration);
        const tlva = mmns.typedecls.find((tdecl) => tdecl.name === "Tree") as DatatypeTypeDecl;
        const vtype = new NominalTypeSignature(tdecl.sinfo, undefined, tlva, [rcvr.alltermargs[0], rcvr.alltermargs[1]]);
        
        const metypedecl = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "MapEntry") as AbstractNominalTypeDecl;
        const metype = new NominalTypeSignature(tdecl.sinfo, undefined, metypedecl, rcvr.alltermargs);

        const emptyconstdecl = mmns.functions.find((ff) => ff.name === "s_map_create_empty") as NamespaceFunctionDecl;
        const pushdecl = mmns.functions.find((ff) => ff.name === "s_map_insert") as NamespaceFunctionDecl;
        const emptyconst = EmitNameManager.generateAccssorNameForNamespaceFunction(this.currentns as NamespaceDeclaration, mmns, emptyconstdecl, rcvr.alltermargs) + "()";
        const pushcall = EmitNameManager.generateAccssorNameForNamespaceFunction(this.currentns as NamespaceDeclaration, mmns, pushdecl, [rcvr.alltermargs[0], rcvr.alltermargs[1]]);
        const pedecls = [
            `$parseAPI: { value: (parser) => { parser.checkConsType("${rcvr.tkeystr}"); const ee = parser.parseCollectionConsArgs("${metype.tkeystr}"); return ee.reduce((acc, v) => { return ${pushcall}(acc, v.key, v.value); }, ${emptyconst}); } }`,
            `$emitAPI: { value: (emitter, value) => { return "${rcvr.tkeystr}" + "{" + emitter.emitCollectionEntries("MapEntry<${rcvr.alltermargs[0].tkeystr}, ${rcvr.alltermargs[1].tkeystr}>", value.value) + "}"; } }`
        ];

        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: vtype}], undefined, false, pedecls, undefined);
    }

    private emitEventListTypeDecl(ns: NamespaceDeclaration, tdecl: EventListTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined, false, [], undefined);
    }

    private emitEntityTypeDecl(ns: NamespaceDeclaration, tdecl: EntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, true, fmt);
        fmt.indentPush();
        const declsfmt = rr.map((dd) => fmt.indent(dd)).join("," + fmt.nl());
        fmt.indentPop();

        const obj = `Object.create($VRepr, {${fmt.nl()}${declsfmt}${fmt.nl()}${fmt.indent("})")}`;

        if(tdecl.terms.length !== 0) {
            return `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`;
        }
        else {
            if(ns.isTopNamespace()) {
                return `export const ${tdecl.name} = ${obj}`;
            }
            else {
                return `${tdecl.name}: ${obj}`;
            }
        }
    }

    private emitOptionTypeDecl(ns: NamespaceDeclaration, tdecl: OptionTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);

        const somedecl = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Some") as AbstractNominalTypeDecl;
        const sometype = new NominalTypeSignature(tdecl.sinfo, undefined, somedecl, rcvr.alltermargs);

        const pedecls = [
            `$parseAPI: { value: (parser) => { return parser.testAndConsumeIfNone() ? _$None : parser.parseValue("${sometype.tkeystr}"); } }`,
            `$emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }`
        ];

        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [{fname: "value", ftype: rcvr.alltermargs[0]}], undefined, false, pedecls, undefined);
    }

    private emitResultTypeDecl(ns: NamespaceDeclaration, tdecl: ResultTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        fmt.indentPush();
        const okdecl = this.emitOkTypeDecl(ns, tdecl.getOkType(), instantiation, fmt);
        const faildecl = this.emitFailTypeDecl(ns, tdecl.getFailType(), instantiation, fmt);
        fmt.indentPop();

        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        const oktype = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.getOkType(), rcvr.alltermargs);
        const failtype = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl.getFailType(), rcvr.alltermargs);

        const pedecls = [
            `$parseAPI: { value: (parser) => { if(parser.testIfOk()) { return parser.parseValue("${oktype.tkeystr}"); } else if(parser.testIfFail()) { return parser.parseValue("${failtype.tkeystr}"); } else { return parser.parseValue(parser.peekScopedType()); } } }`,
            `$emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }`
        ];

        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, undefined, undefined, false, [okdecl, faildecl, ...pedecls], undefined);
    }

    private emitAPIResultTypeDecl(ns: NamespaceDeclaration, tdecl: APIResultTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        fmt.indentPush();
        const rejecteddecl = this.emitAPIRejectedTypeDecl(ns, tdecl.getAPIRejectedType(), instantiation, fmt);
        const faileddecl = this.emitAPIFailedTypeDecl(ns, tdecl.getAPIFailedType(), instantiation, fmt);
        const errordecl = this.emitAPIErrorTypeDecl(ns, tdecl.getAPIErrorType(), instantiation, fmt);
        const successdecl = this.emitAPISuccessTypeDecl(ns, tdecl.getAPISuccessType(), instantiation, fmt);
        fmt.indentPop();

        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);

        const pedecls = [
            `$parseAPI: { value: (parser) => { return parser.parseValue(parser.peekScopedType()); } }`,
            `$emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }`
        ];

        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, undefined, undefined, false, [rejecteddecl, faileddecl, errordecl, successdecl, ...pedecls], undefined);
    }

    private emitConceptTypeDecl(ns: NamespaceDeclaration, tdecl: ConceptTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, false, fmt);

        const pedecls = [
            `$parseAPI: { value: (parser) => { return parser.parseValue(parser.peekScopedType()); } }`,
            `$emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }`
        ];
            
        fmt.indentPush();
        const declsfmt = [...rr, ...pedecls].map((dd) => fmt.indent(dd)).join("," + fmt.nl());
        fmt.indentPop();

        const obj = `Object.create(Object.prototype, {${fmt.nl()}${declsfmt}${fmt.nl()}${fmt.indent("})")}`;

        if(tdecl.terms.length !== 0) {
            return `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`;
        }
        else {
            if(ns.isTopNamespace()) {
                return `export const ${tdecl.name} = ${obj}`;
            }
            else {
                return `${tdecl.name}: ${obj}`;
            }
        }
    }

    private emitDatatypeMemberEntityTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeMemberEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, true, fmt);
        fmt.indentPush();
        const declsfmt = rr.map((dd) => fmt.indent(dd)).join("," + fmt.nl());
        fmt.indentPop();

        const obj = `Object.create($VRepr, {${fmt.nl()}${declsfmt}${fmt.nl()}${fmt.indent("})")}`;

        if(tdecl.terms.length !== 0) {
            return `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`;
        }
        else {
            if(ns.isTopNamespace()) {
                return `export const ${tdecl.name} = ${obj}`;
            }
            else {
                return `${tdecl.name}: ${obj}`;
            }
        }
    }

    private emitDatatypeTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, false, fmt);

        const pedecls = [
            `$parseAPI: { value: (parser) => { return parser.parseValue(parser.peekScopedType()); } }`,
            `$emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }`
        ];

        fmt.indentPush();
        const declsfmt = [...rr, ...pedecls].map((dd) => fmt.indent(dd)).join("," + fmt.nl());
        fmt.indentPop();

        const obj = `Object.create(Object.prototype, {${fmt.nl()}${declsfmt}${fmt.nl()}${fmt.indent("})")}`;

        if(tdecl.terms.length !== 0) {
            return `${EmitNameManager.emitTypeTermKey(rcvr)}: ${obj}`;
        }
        else {
            if(ns.isTopNamespace()) {
                return `export const ${tdecl.name} = ${obj}`;
            }
            else {
                return `${tdecl.name}: ${obj}`;
            }
        }
    }

    private emitAPIDecls(ns: NamespaceDeclaration, adecls: APIDecl[], fmt: JSCodeFormatter): string[] {
        if(adecls.length !== 0) {
            assert(false, "Not implemented -- checkAPIDecl");
        }

        return [];
    }

    private emitTaskDecls(ns: NamespaceDeclaration, tdecls: TaskDecl[], fmt: JSCodeFormatter): string[] {
        if(tdecls.length !== 0) {
            assert(false, "Not implemented -- checkTaskDecl");
        }

        return [];
    }

    private emitNamespaceConstDecls(inns: NamespaceDeclaration, decls: NamespaceConstDecl[], fmt: JSCodeFormatter): string[] {
        let cdecls: string[] = [];
        for(let i = 0; i < decls.length; ++i) {
            const m = decls[i];

            this.currentfile = m.file;
            const eexp = this.emitExpression(m.value.exp, true);
            const lexp = `() => ${eexp}`;

            const fmtstyle = inns.isTopNamespace() ? `export function ${m.name}()` : `${m.name}: () =>`;
            cdecls.push(`${fmtstyle} { return _$memoconstval(_$consts, "${inns.fullnamespace.emit() + "::" + m.name}", ${lexp}); }`);
        }

        return cdecls;
    }

    private emitTypeSubtypeRelation(tdecl: AbstractNominalTypeDecl, instantiation: TypeInstantiationInfo): string {
        if((tdecl instanceof PrimitiveEntityTypeDecl) && tdecl.name === "None") {
            return "//_$supertypes for none is a special case in code (not emitted)";
        }
        else {
            this.mapper = instantiation.binds;
            const supers = tdecl.saturatedProvides.map((ss) => `Symbol.for("${this.tproc(ss).tkeystr}")`).join(", ");
            this.mapper = undefined;

            return `_$supertypes[Symbol.for("${instantiation.tkey}")] = [${supers}].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});`;
        }
    }

    private isMultiEmitDecl(tdecl: AbstractNominalTypeDecl): boolean {
        if(tdecl.terms.length !== 0) {
            return true;
        }
        else {
            return tdecl.isSpecialResultEntity() || tdecl.isSpecialAPIResultEntity() || (tdecl instanceof SomeTypeDecl);
        }
    }

    private emitNamespaceTypeDecls(ns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl[], asminstantiation: NamespaceInstantiationInfo, fmt: JSCodeFormatter): {decls: string[], supers: string[], parses: string[], emits: string[]} {
        let alldecls: string[] = [];
        let allsupertypes: string[] = [];
        let allparsedecls: string[] = [];
        let allemitdecls: string[] = [];

        for(let i = 0; i < tdecl.length; ++i) {
            const tt = tdecl[i];
            const iinsts = asminstantiation.typebinds.get(tt.name);
            if(iinsts === undefined) {
                continue;
            }

            this.currentfile = tt.file;
            if(this.isMultiEmitDecl(tt)) {
                fmt.indentPush();
            }
            
            let ddecls: string[] = [];
            for(let j = 0; j < iinsts.length; ++j) {
                const instantiation = iinsts[j];

                if(tt instanceof EnumTypeDecl) {
                    const decl = this.emitEnumTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof TypedeclTypeDecl) {
                    const decl = this.emitTypedeclTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof PrimitiveEntityTypeDecl) {
                    const decl = this.emitPrimitiveEntityTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof OkTypeDecl) {
                    const decl = this.emitOkTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof FailTypeDecl) {
                    const decl = this.emitFailTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof APIRejectedTypeDecl) {
                    const decl = this.emitAPIRejectedTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof APIFailedTypeDecl) {
                    const decl = this.emitAPIFailedTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof APIErrorTypeDecl) {
                    const decl = this.emitAPIErrorTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof APISuccessTypeDecl) {
                    const decl = this.emitAPISuccessTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof SomeTypeDecl) {
                    const decl = this.emitSomeTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof MapEntryTypeDecl) {
                    const decl = this.emitMapEntryTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof ListTypeDecl) {
                    const decl = this.emitListTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof StackTypeDecl) {
                    const decl = this.emitStackTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof QueueTypeDecl) {
                    const decl = this.emitQueueTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof SetTypeDecl) {
                    const decl = this.emitSetTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof MapTypeDecl) {
                    const decl = this.emitMapTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof EventListTypeDecl) {
                    const decl = this.emitEventListTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof EntityTypeDecl) {
                    const decl = this.emitEntityTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof OptionTypeDecl) {
                    const decl = this.emitOptionTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof ResultTypeDecl) {
                    const decl = this.emitResultTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof APIResultTypeDecl) {
                    const decl = this.emitAPIResultTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof ConceptTypeDecl) {
                    const decl = this.emitConceptTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof DatatypeMemberEntityTypeDecl) {
                    const decl = this.emitDatatypeMemberEntityTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else if(tt instanceof DatatypeTypeDecl) {
                    const decl = this.emitDatatypeTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                }
                else {
                    assert(false, "Unknown type decl kind");
                }

                if(tt instanceof AbstractEntityTypeDecl) {
                    allsupertypes.push(this.emitTypeSubtypeRelation(tt, instantiation));
                }
                else {
                    if(tt instanceof ResultTypeDecl) {
                        allsupertypes.push(this.emitTypeSubtypeRelation(tt.getOkType(), instantiation));
                        allsupertypes.push(this.emitTypeSubtypeRelation(tt.getFailType(), instantiation));
                    }

                    if(tt instanceof APIResultTypeDecl) {
                        allsupertypes.push(this.emitTypeSubtypeRelation(tt.getAPIRejectedType(), instantiation));
                        allsupertypes.push(this.emitTypeSubtypeRelation(tt.getAPIFailedType(), instantiation));
                        allsupertypes.push(this.emitTypeSubtypeRelation(tt.getAPIErrorType(), instantiation));
                        allsupertypes.push(this.emitTypeSubtypeRelation(tt.getAPISuccessType(), instantiation));
                    }
                }

                if(!(tt instanceof PrimitiveEntityTypeDecl)) {
                    allparsedecls.push(`_$parsemap["${instantiation.tkey}"] = ${EmitNameManager.generateAccessorForParseFunction(this.currentns as NamespaceDeclaration, instantiation.tsig as NominalTypeSignature)};`);
                    allemitdecls.push(`_$emitmap["${instantiation.tkey}"] = ${EmitNameManager.generateAccessorForEmitFunction(this.currentns as NamespaceDeclaration, instantiation.tsig as NominalTypeSignature)};`);
                }
            }

            if(!this.isMultiEmitDecl(tt)) {
                if(ns.isTopNamespace()) {
                    alldecls.push(fmt.indent(ddecls[0] + ";"));
                }
                else {
                    alldecls.push(ddecls[0]);
                }
            }
            else {
                const dclstr = ddecls.map((dd) => fmt.indent(dd)).join("," + fmt.nl());
                
                fmt.indentPop();
                if(ns.isTopNamespace()) {
                    alldecls.push(`export const ${tt.name} = {${fmt.nl()}${dclstr}${fmt.nl()}${fmt.indent("}")}`);
                }
                else {
                    alldecls.push(`${tt.name}: {${fmt.nl()}${dclstr}${fmt.nl()}${fmt.indent("}")}`);
                }
            }
        }

        asminstantiation.elists.forEach((edef, elk) => {
            const elistargs = edef.entries.map((tt) => '"' + tt.tkeystr + '"');
            const eemit = elistargs.map((ttk, i) => `emitter.emitValue(${ttk}, value[${i}])`);
            
            allparsedecls.push(`_$parsemap["${elk}"] = (parser) => parser.parseEListArgs(${elistargs.join(", ")});`);
            allemitdecls.push(`_$emitmap["${elk}"] = (emitter, value) => "(|" + ${eemit.join(" + ")} + "|)";`);
        });
    
        return {decls: alldecls, supers: allsupertypes, parses: allparsedecls, emits: allemitdecls};
    }

    private emitReadArgsFromStdInAndCall(defaultns: string, paramtypes: string[]): string {
        if(paramtypes.length === 0) {
            return "let res; try { res = main(); } catch(e) { process.stdout.write(`Error -- ${e.$info || e}\\n`); process.exit(1); }";
        }
        else {
            const usefile = `const usefile = process.argv.length === 4 && process.argv[2] === "--file";`;
            const input = `import { readFileSync } from "fs";\nlet input = readFileSync(usefile ? process.argv[3] : 0, 'utf-8');`;
            const pdecls = `try { args = _$parseBSQON([${paramtypes.map((tt) => `"${tt}"`).join(", ")}], input); } catch(pe) { process.stdout.write(\`ParseError -- \${pe.message || pe}\\n\`); process.exit(1); }`;
            return `${usefile}\n${input}\nlet args;\n${pdecls}\nlet res;\ntry { res = main(...args); } catch(e) { process.stdout.write(\`Error -- \${e.$info || e}\\n\`); process.exit(1); }`;
        }
    }

    private emitOutputResultToStdOut(tkey: string, mcall: string): string {
        return `process.stdout.write(_$emitBSQON("${tkey}", res) + '\\n');'\\n'`
    }

    private emitNamespaceDeclaration(decl: NamespaceDeclaration, asminstantiation: NamespaceInstantiationInfo, aainsts: NamespaceInstantiationInfo[], mainns: string | undefined, fmt: JSCodeFormatter, isparentTop: boolean): {contents: string, nestedsupers: string[]} {
        //all usings should be resolved and valid so nothing to do there

        let decls: string[] = [];
        let nestedsupers: string[] = [];
        let nestedparses: string[] = [];
        let nestedemits: string[] = [];

        if(!decl.isTopNamespace()) {
            fmt.indentPush();
        }

        for(let i = 0; i < decl.subns.length; ++i) {
            const subdecl = decl.subns[i];
            const nsii = aainsts.find((ai) => ai.ns.emit() === subdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                const cdecl = this.currentns;

                this.currentns = subdecl;
                const snsdecl = this.emitNamespaceDeclaration(decl.subns[i], nsii, aainsts, mainns, fmt, decl.isTopNamespace());
                
                decls.push(snsdecl.contents);
                nestedsupers.push(...snsdecl.nestedsupers);
                nestedparses.push(...snsdecl.nestedsupers);
                nestedemits.push(...snsdecl.nestedsupers);

                this.currentns = cdecl;
            }
        }

        const cdecls = this.emitNamespaceConstDecls(decl, decl.consts, fmt);
        decls.push(...cdecls);

        const fdecls = this.emitFunctionDecls(undefined, decl.functions.map((fd) => [fd, asminstantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls);

        const tdecls = this.emitNamespaceTypeDecls(decl, decl.typedecls, asminstantiation, fmt);
        decls.push(...tdecls.decls);

        const apidecls = this.emitAPIDecls(decl, decl.apis, fmt);
        decls.push(...apidecls);

        const taskdecls = this.emitTaskDecls(decl, decl.tasks, fmt);
        decls.push(...taskdecls);

        if(decl.isTopNamespace()) {
            const ddecls = decls.join(fmt.nl(2));
            let supers = "";
            if(tdecls.supers.length !== 0 || nestedsupers.length !== 0) {
                supers = fmt.nl(2) + [...tdecls.supers, ...nestedsupers].join(fmt.nl());
            }

            let parses = "";
            if(tdecls.parses.length !== 0) {
                parses = fmt.nl(2) + [...tdecls.parses, ...nestedparses].join(fmt.nl());
            }

            let emits = "";
            if(tdecls.emits.length !== 0) {
                emits = fmt.nl(2) + [...tdecls.emits, ...nestedemits].join(fmt.nl());
            }

            let imports = "";
            for(let i = 0; i < decl.usings.length; ++i) {
                const tlname = decl.usings[i].fromns;
                if(decl.name !== tlname && aainsts.find((ai) => ai.ns.ns[0] === tlname) !== undefined) {
                    imports += `import * as $${tlname} from "./${tlname}.mjs";${fmt.nl()}`;
                }
            }
            if(decl.name !== "Core") {
                imports += `import * as $Core from "./Core.mjs";${fmt.nl(2)}`;
            }

            imports += ("let _$rv = {};" + fmt.nl(2));

            let loadop = "";
            let mainop = fmt.nl();
            if(decl.name === mainns) {
                const asmreinfo = this.assembly.toplevelNamespaces.flatMap((ns) => this.assembly.loadConstantsAndValidatorREs(ns));

                //Now process the regexs
                loadop = `\n\nimport { loadConstAndValidateRESystem } from "@bosque/jsbrex";${fmt.nl()}loadConstAndValidateRESystem(${JSON.stringify(asmreinfo, undefined, 4)});`
                
                const mainf = decl.functions.find((fd) => fd.name === "main");
                if(mainf === undefined) {
                    mainop = "\nprocess.stdout.write(`Error -- main function not found in main namespace\\n`);";
                }
                else {
                    const params = this.emitReadArgsFromStdInAndCall(decl.name, mainf.params.map((pt) => pt.type.tkeystr));
                    const op = this.emitOutputResultToStdOut(mainf.resultType.tkeystr, "main");

                    mainop = `\n${params}${fmt.nl()}${op}`;
                }
            }

            return {contents: prefix + imports + ddecls + supers + parses + emits + loadop + mainop, nestedsupers: []};
        }
        else {
            const idecls = decls.map((dd) => fmt.indent(dd)).join("," + fmt.nl());
            fmt.indentPop();

            let ddecls = "";
            if(isparentTop) {
                ddecls = fmt.indent(`export const ${decl.name} = {${fmt.nl()}${idecls}${fmt.nl()}${fmt.indent("};")}`);
            }
            else {
                ddecls = fmt.indent(`${decl.name}: {${fmt.nl()}${idecls}${fmt.nl()}${fmt.indent("}")}`);
            }

            return {contents: ddecls, nestedsupers: tdecls.supers};
        }
    }

    static emitAssembly(assembly: Assembly, mode: "release" | "debug", buildlevel: BuildLevel, mainns: string, asminstantiation: NamespaceInstantiationInfo[]): {ns: FullyQualifiedNamespace, contents: string}[] {
        const emitter = new JSEmitter(assembly, asminstantiation, mode == "release" ? "release" : "debug", buildlevel, false, undefined, undefined);

        //emit each of the assemblies
        let results: {ns: FullyQualifiedNamespace, contents: string}[] = [];
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            const nsdecl = assembly.toplevelNamespaces[i];
            const nsii = asminstantiation.find((ai) => ai.ns.emit() === nsdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                emitter.currentns = nsdecl;
                const code = emitter.emitNamespaceDeclaration(nsdecl, nsii, asminstantiation, mainns, new JSCodeFormatter(0), true);

                results.push({ns: nsdecl.fullnamespace, contents: code.contents});
            }
        }

        return results;
    }

    static emitTestAssembly(assembly: Assembly, asminstantiation: NamespaceInstantiationInfo[], testfilefilter: string[] | undefined, testfilters: TestAssociation[] | undefined): [{ns: FullyQualifiedNamespace, contents: string}[], string] {
        const emitter = new JSEmitter(assembly, asminstantiation, "debug", "test", true, testfilefilter, testfilters);
        
        //emit each of the assemblies
        let results: {ns: FullyQualifiedNamespace, contents: string}[] = [];
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            const nsdecl = assembly.toplevelNamespaces[i];
            const nsii = asminstantiation.find((ai) => ai.ns.emit() === nsdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                emitter.currentns = nsdecl;
                const code = emitter.emitNamespaceDeclaration(nsdecl, nsii, asminstantiation, undefined, new JSCodeFormatter(0), true);

                results.push({ns: nsdecl.fullnamespace, contents: code.contents});
            }
        }

        let tgs: string[] = [];
        let totalcount = 0;
        for(let i = 0; i < emitter.testgroups.length; ++i) {
            const tg = emitter.testgroups[i];
            totalcount += tg[1].length;

            const ttests = tg[1].join("\n");
            tgs.push(`process.stdout.write("\\nRunning tests from ${tg[0]} (${i + 1}/${emitter.testgroups.length})\\n");\n` + ttests);
        }

        let imports = "";
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            const tlname = assembly.toplevelNamespaces[i].name;
            if(asminstantiation.find((ai) => ai.ns.ns[0] === tlname) !== undefined) {
                imports += `import * as $${tlname} from "./${tlname}.mjs";\n`;
            }
        }

        const tgheader = prefix + imports + "\n";

        const asmreinfo = assembly.toplevelNamespaces.flatMap((ns) => assembly.loadConstantsAndValidatorREs(ns));
        const loadop = `import { loadConstAndValidateRESystem } from "@bosque/jsbrex";\nloadConstAndValidateRESystem(${JSON.stringify(asmreinfo, undefined, 4)});\n\n`
                
        const vinit = `let _$ccount = 0;\nlet _$passcount = 0;\nlet _$failcount = 0;\nlet _$errorcount = 0;\nconst _$totalcount = ${totalcount}\n\n`;
        const tests = tgs.join("\n\n") + "\n\n";

        const verrors = `if(_$errorcount !== 0) { process.stdout.write(_$errorcount.toString() + " tests had errors...\\n") }\n`;
        const vfails = `if(_$failcount !== 0) { process.stdout.write(_$failcount.toString() + " tests failed...\\n") }\n`;
        const vok = `if(_$errorcount === 0 && _$failcount === 0) { process.stdout.write("All (" + _$passcount.toString() + ") tests passed!\\n"); process.exit(0); } else { process.stdout.write(_$passcount.toString() + " tests passed...\\ndone\\n"); process.exit(1); }\n`;

        return [results, tgheader + loadop + vinit + tests + verrors + vfails + vok];
    }
}

export {
    JSEmitter
};
