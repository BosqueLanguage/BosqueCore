import assert from "node:assert";

import { JSCodeFormatter, EmitNameManager } from "./jsemitter_support.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, DebugStatement, EmptyStatement, EnvironmentBracketStatement, EnvironmentUpdateStatement, Expression, ExpressionBodyImplementation, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, ITestFail, ITestNone, ITestOk, ITestSome, ITestType, LambdaInvokeExpression, LetExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PostfixProjectFromNames, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SelfUpdateStatement, SpecialConstructorExpression, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, SynthesisBodyImplementation, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskEventEmitStatement, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VarUpdateStatement, VoidRefCallStatement } from "../frontend/body.js";
import { AbstractCollectionTypeDecl, AbstractNominalTypeDecl, APIDecl, APIErrorTypeDecl, APIFailedTypeDecl, APIRejectedTypeDecl, APIResultTypeDecl, APISuccessTypeDecl, Assembly, ConceptTypeDecl, ConstMemberDecl, ConstructableTypeDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, EntityTypeDecl, EnumTypeDecl, FailTypeDecl, EventListTypeDecl, FunctionInvokeDecl, InternalEntityTypeDecl, InvariantDecl, InvokeExample, InvokeExampleDeclFile, InvokeExampleDeclInline, InvokeParameterDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, OkTypeDecl, OptionTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResultTypeDecl, SetTypeDecl, SomeTypeDecl, StackTypeDecl, TaskDecl, TypedeclTypeDecl, TypeFunctionDecl, ValidateDecl, AbstractEntityTypeDecl } from "../frontend/assembly.js";
import { FullyQualifiedNamespace, NominalTypeSignature, TemplateNameMapper, TemplateTypeSignature, TypeSignature } from "../frontend/type.js";
import { BuildLevel, CodeFormatter, isBuildLevelEnabled, SourceInfo } from "../frontend/build_decls.js";
import { NamespaceInstantiationInfo, FunctionInstantiationInfo, MethodInstantiationInfo, TypeInstantiationInfo } from "../frontend/instantiation_map.js";

const prefix = 
'"use strict";\n' +
'const JSMap = Map;\n' +
'\n' +
'import {_$softfails, _$supertypes, _$b, _$rc_i, _$rc_n, _$rc_N, _$rc_f, _$dc_i, _$dc_n, _$dc_I, _$dc_N, _$dc_f, _$abort, _$assert, _$formatchk, _$invariant, _$validate, _$precond, _$softprecond, _$postcond, _$softpostcond, _$memoconstval, _$accepts} from "./runtime.mjs";\n' +
'\n'
;

class JSEmitter {
    readonly assembly: Assembly;
    readonly mode: "release" | "debug";
    readonly buildlevel: BuildLevel;
    readonly generateTestInfo: boolean;

    currentfile: string | undefined;
    currentns: NamespaceDeclaration | undefined;

    mapper: TemplateNameMapper | undefined;
    returncompletecall: string | undefined = undefined;

    bindernames: Set<string> = new Set();

    constructor(assembly: Assembly, mode: "release" | "debug", buildlevel: BuildLevel, generateTestInfo: boolean) {
        this.assembly = assembly;
        this.mode = mode;
        
        this.buildlevel = buildlevel;
        this.generateTestInfo = generateTestInfo;

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

    private emitBoxOperation(val: string, oftype: NominalTypeSignature): string {
        const taccess = EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), oftype);
        return `_$b(${taccess}, ${val})`;
    }

    private emitUnBoxOperation(val: string): string {
        return `(${val}).$val`;
    }

    private emitBUAsNeeded(val: string, oftype: TypeSignature, totype: TypeSignature): string {
        const oftypet = this.tproc(oftype);
        const totypet = this.tproc(totype);

        if(EmitNameManager.isNakedTypeRepr(oftypet)) {
            if(EmitNameManager.isNakedTypeRepr(totypet)) {
                return val;
            }
            else {
                return this.emitBoxOperation(val, oftypet as NominalTypeSignature);
            }
        }
        else {
            assert(EmitNameManager.isBoxedTypeRepr(oftypet), "expected boxed type repr");

            if(EmitNameManager.isBoxedTypeRepr(totypet)) {
                return val;
            }
            else {
                return this.emitUnBoxOperation(val);
            }
        }
    }

    private emitITestAsTest_None(val: string, isnot: boolean): string {
        return val + (isnot ? "._$isSome()" : "._$isNone()");
    }

    private emitITestAsTest_Some(val: string, isnot: boolean): string {
        return val + (isnot ? "._$isNone()" : "._$isSome()");
    }

    private emitITestAsTest_Ok(val: string, vtype: TypeSignature, isnot: boolean): string {
        const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
        const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
        const failtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getFailType(), (vtype as NominalTypeSignature).alltermargs);

        return `${val}._$is(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), isnot ? failtype : oktype)})`;
    }

    private emitITestAsTest_Fail(val: string, vtype: TypeSignature, isnot: boolean): string {
        const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
        const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
        const failtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getFailType(), (vtype as NominalTypeSignature).alltermargs);

        return `${val}._$is(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), isnot ? oktype : failtype)})`;
    }

    private emitITestAsTest_Type(val: string, oftype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isUniqueTypeForSubtypeChecking(oftype)) {
            return `${val}._$is${isnot ? "Not" : ""}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), this.tproc(oftype) as NominalTypeSignature)})`;
        }
        else {
            return `${val}._$is${isnot ? "Not" : ""}Subtype(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), this.tproc(oftype) as NominalTypeSignature)})`;
        }
    }
    
    private processITestAsTest(val: string, vtype: TypeSignature, tt: ITest): string {
        const vvtype = this.tproc(vtype);
        
        if(tt instanceof ITestType) {
            return this.emitITestAsTest_Type(val, tt.ttype, tt.isnot);
        }
        else {
            if(tt instanceof ITestNone) {
                return this.emitITestAsTest_None(val, tt.isnot);
            }
            else if(tt instanceof ITestSome) {
                return this.emitITestAsTest_Some(val, tt.isnot);
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
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const emsg = this.getErrorInfo(isnot ? "expected None but got Some" : "expected Some but got None", sinfo, undefined);
            return val + (isnot ? `._$asSome(${emsg})` : `._$asNone(${emsg})`);
        }
    }

    private emitITestAsConvert_Some(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const emsg = this.getErrorInfo(isnot ? "expected Some but got None" : "expected None but got Some", sinfo, undefined);
            return val + (isnot ? `._$asNone(${emsg})` : `._$asSome(${emsg})`);
        }
    }

    private emitITestAsConvert_Ok(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
            const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
            const failtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getFailType(), (vtype as NominalTypeSignature).alltermargs);

            const emsg = this.getErrorInfo(isnot ? "expected Err but got Ok" : "expected Ok but got Err", sinfo, undefined);
            return `${val}._$as(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), isnot ? failtype : oktype)}, true, ${emsg})`;
        }
    }

    private emitITestAsConvert_Fail(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
            const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
            const failtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getFailType(), (vtype as NominalTypeSignature).alltermargs);

            const emsg = this.getErrorInfo(isnot ? "expected Ok but got Err" : "expected Err but got Ok", sinfo, undefined);
            return `${val}._$as(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), isnot ? oktype : failtype)}, true, ${emsg})`;
        }
    }

    private emitITestAsConvert_Type(sinfo: SourceInfo, val: string, vtype: TypeSignature, oftype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return EmitNameManager.isBoxedTypeRepr(oftype) ? `_$b${val}` : val;
        }
        else {
            const ubx = EmitNameManager.isNakedTypeRepr(oftype);
            if(EmitNameManager.isUniqueTypeForSubtypeChecking(oftype)) {
                const toftype = this.tproc(oftype) as NominalTypeSignature;
                const emsg = this.getErrorInfo(isnot ? `expected different type than ${toftype.tkeystr}` : `expected type ${toftype.tkeystr}`, sinfo, undefined);
                return `${val}._$as${isnot ? "Not" : ""}(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), toftype)}, ${ubx}, ${emsg})`;
            }
            else {
                const toftype = this.tproc(oftype) as NominalTypeSignature;
                const emsg = this.getErrorInfo(isnot ? `expected not subtype of ${toftype.tkeystr}` : `expected subtytype of ${toftype.tkeystr}`, sinfo, undefined);
                return `${val}._$as${isnot ? "Not" : ""}Subtype(${EmitNameManager.generateAccessorForTypeKey(this.getCurrentNamespace(), toftype)}, ${ubx}, ${emsg})`;
            }
        }
    }
    
    private processITestAsConvert(sinfo: SourceInfo, val: string, vtype: TypeSignature, tt: ITest): string {
        const vvtype = this.tproc(vtype);
        
        if(tt instanceof ITestType) {
            return this.emitITestAsConvert_Type(sinfo, val, vvtype, this.tproc(tt.ttype), tt.isnot);
        }
        else {
            if(tt instanceof ITestNone) {
                return this.emitITestAsConvert_None(sinfo, val, vvtype, tt.isnot);
            }
            else if(tt instanceof ITestSome) {
                return this.emitITestAsConvert_Some(sinfo, val, vvtype, tt.isnot);
            }
            else if(tt instanceof ITestOk) {
                return this.emitITestAsConvert_Ok(sinfo, val, vvtype, tt.isnot);
            }
            else {
                assert(tt instanceof ITestFail, "missing case in ITest");
                return this.emitITestAsConvert_Fail(sinfo, val, vvtype, tt.isnot);
            }
        }
    }

    private emitLiteralNoneExpression(): string {
        return "null";
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
        return `${exp.value}.slice(0, -1)`;
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
        if(exp.isDirectLiteral) {
            return this.emitExpression(exp.value, toplevel);
        }
        else {
            const taccess = EmitNameManager.generateAccessorForTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.constype) as NominalTypeSignature);
            return `${taccess}(${this.emitExpression(exp.value, true)})`;
        }
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
        assert(false, "Not implemented -- AccessStaticField");
    }
    
    private emitAccessVariableExpression(exp: AccessVariableExpression): string {
        let aname: string;

        if(!exp.isCaptured) {
            if(exp.srcname === "this") {
                aname = "_$this";
            }
            else if(exp.srcname === "self") {
                aname = "_$self";
            }
            else {
                aname = exp.scopename;
            }
        }
        else {
            aname = exp.scopename;
        }

        return this.emitBUAsNeeded(aname, exp.layouttype as TypeSignature, exp.getType());
    }
    
    private emitCollectionConstructor(cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): string {
        if(cdecl instanceof ListTypeDecl) {
            assert(false, "Not implemented -- List"); //TODO: need to implement list in Bosque core + have way well known way to call constructor here!!!!
        }
        else {
            assert(false, "Unknown collection type -- emitCollectionConstructor");
        }
    }

    private emitSpecialConstructableConstructor(cdecl: ConstructableTypeDecl, exp: ConstructorPrimaryExpression, toplevel: boolean): string {
        if(cdecl instanceof MapEntryTypeDecl) {
            const metype = exp.ctype as NominalTypeSignature;
            const meargs = exp.args.args;
            const m0exp = this.emitBUAsNeeded(this.emitExpression(meargs[0].exp, true),  meargs[0].exp.getType(), metype.alltermargs[0]);
            const m1exp = this.emitBUAsNeeded(this.emitExpression(meargs[1].exp, true),  meargs[1].exp.getType(), metype.alltermargs[1]);
            return `[${m0exp}, ${m1exp}]`;
        }
        else {
            const pexp = exp.args.args[0].exp;
            return this.emitBUAsNeeded(this.emitExpression(pexp, toplevel), pexp.getType(), exp.getType());
        }
    }

    private emitTypeDeclConstructor(cdecl: TypedeclTypeDecl, exp: ConstructorPrimaryExpression, toplevel: boolean): string {
        if(!exp.hasChecks) {
            return this.emitExpression(exp.args.args[0].exp, toplevel);
        }
        else {
            const earg = this.emitExpression(exp.args.args[0].exp, true);
            const taccess = EmitNameManager.generateAccessorForTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.ctype) as NominalTypeSignature);
            
            return `${taccess}(${earg})`;
        }
    }

    private emitStandardConstructor(exp: ConstructorPrimaryExpression): string {
        const taccess = EmitNameManager.generateAccessorForTypeConstructor(this.getCurrentNamespace(), this.tproc(exp.ctype) as NominalTypeSignature);

        const aargs: string[] = [];
        for(let i = 0; i < exp.shuffleinfo.length; ++i) {
            const ii = exp.shuffleinfo[i];
            if(ii[0] === -1) {
                aargs.push("undefined");
            }
            else {
                const aaexp = this.emitBUAsNeeded(this.emitExpression(exp.args.args[ii[0]].exp, true), exp.args.args[ii[0]].exp.getType(), ii[2]);
                aargs.push(aaexp);
            }
        }

        if(!exp.hasChecks && exp.shuffleinfo.every((ii) => ii[0] !== -1)) {
            let iargs: string[] = [];

            for(let i = 0; i < aargs.length; ++i) {
                iargs.push(`${exp.shuffleinfo[i][1]}: ${aargs[i]}`);
            }

            return `{${iargs.join(", ")}}`;
        }
        else {
            return `${taccess}(${aargs.join(", ")})`;
        }
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
        assert(false, "Not implemented -- ConstructorEList");
    }
    
    private emitConstructorLambdaExpression(exp: ConstructorLambdaExpression): string {
        assert(false, "Not implemented -- ConstructorLambda");
    }

    private emitLetExpression(exp: LetExpression): string {
        assert(false, "Not implemented -- Let");
    }

    private emitLambdaInvokeExpression(exp: LambdaInvokeExpression): string {
        assert(false, "Not implemented -- LambdaInvoke");
    }

    private emitSpecialConstructorExpression(exp: SpecialConstructorExpression, toplevel: boolean): string {
        return this.emitBUAsNeeded(this.emitExpression(exp.arg, toplevel), exp.constype as TypeSignature, exp.getType());
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
                const aaexp = this.emitBUAsNeeded(this.emitExpression(exp.args.args[ii[0]].exp, true), exp.args.args[ii[0]].exp.getType(), ii[1] as TypeSignature);
                argl.push(aaexp);
            }
        }

        if(exp.restinfo !== undefined) {
            const restl: string[] = [];

            for(let i = 0; i < exp.restinfo.length; ++i) {
                const rri = exp.restinfo[i];
                if(!rri[1]) {
                    const rrexp = this.emitBUAsNeeded(this.emitExpression(exp.args.args[rri[0]].exp, true), exp.args.args[rri[0]].exp.getType(), rri[2] as TypeSignature);
                    restl.push(rrexp);
                }
                else {
                    assert(false, "Not implemented -- CallNamespaceFunction -- spread into rest");
                }
            }

            const invk = cns.functions.find((f) => f.name === exp.name) as NamespaceFunctionDecl;
            const rparams = invk.params[invk.params.length - 1];
            if((rparams.type as NominalTypeSignature).decl instanceof ListTypeDecl) {
                assert(false, "Not implemented -- List");
                //argl.push(`[${restl.join(", ")}]`);
            }
            else {
                assert(false, "Not implemented -- CallNamespaceFunction -- rest");
            }
        }

        return `${EmitNameManager.generateAccssorNameForNamespaceFunction(this.getCurrentNamespace(), cns, ffinv, this.mapper)}(${argl.join(", ")})`;
    }
    
    private emitCallTypeFunctionExpression(exp: CallTypeFunctionExpression): string {
        assert(false, "Not implemented -- CallTypeFunction");
    }
    
    private emitLogicActionAndExpression(exp: LogicActionAndExpression): string {
        assert(false, "Not implemented -- LogicActionAnd");
    }
    
    private emitLogicActionOrExpression(exp: LogicActionOrExpression): string {
        assert(false, "Not implemented -- LogicActionOr");
    }
    
    private emitParseAsTypeExpression(exp: ParseAsTypeExpression): string {
        assert(false, "Not implemented -- ParseAsType");
    }

    private emitPostfixAccessFromName(val: string, exp: PostfixAccessFromName): string {
        const rcvrtype = this.tproc(exp.getRcvrType());

        let bbase = "";
        if(EmitNameManager.isNakedTypeRepr(rcvrtype)) {
            bbase = `${val}`;
        }
        else {
            bbase = `${val}.$val`;
        }

        const fdecl = exp.fieldDecl as MemberFieldDecl;
        if(!fdecl.isSpecialAccess) {
            return `${bbase}.${fdecl.name}`;
        }
        else {
            const declin = exp.declaredInType as NominalTypeSignature;
            if(declin.decl instanceof MapEntryTypeDecl) {
                return `${bbase}[${fdecl.name === "key" ? 0 : 1}]`;
            }
            else {
                return bbase; //special case thing
            }
        }
    }

    private emitPostfixProjectFromNames(val: string, exp: PostfixProjectFromNames): string {
        assert(false, "Not Implemented -- emitPostfixProjectFromNames");
    }

    private emitPostfixAccessFromIndex(val: string, exp: PostfixAccessFromIndex): string {
        assert(false, "Not Implemented -- emitPostfixAccessFromIndex");
    }

    private emitPostfixIsTest(val: string, exp: PostfixIsTest): string {
        return this.processITestAsTest(val, this.tproc(exp.getRcvrType()), exp.ttest);
    }

    private emitPostfixAsConvert(val: string, exp: PostfixAsConvert): string {
        return this.processITestAsConvert(exp.sinfo, val, this.tproc(exp.getRcvrType()), exp.ttest);
    }

    private emitPostfixAssignFields(val: string, exp: PostfixAssignFields): string {
        assert(false, "Not Implemented -- emitPostfixAssignFields");
    }

    private emitPostfixInvoke(val: string, exp: PostfixInvoke): string {
        assert(false, "Not Implemented -- emitPostfixInvoke");
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
        const eexp = `!${this.emitExpression(exp.exp, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }

    private emitPrefixNegateOrPlusOpExpression(exp: PrefixNegateOrPlusOpExpression, toplevel: boolean): string {
        if(exp.op === "+") {
            return this.emitExpression(exp.exp, toplevel);
        }
        else {
            const eexp = `${exp.op}${this.emitExpression(exp.exp, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
    }

    private emitBinOpratorExpression(sinfo: SourceInfo, lhs: Expression, rhs: Expression, oprtype: string, op: string, toplevel: boolean): string {
        const eemsg = this.getErrorInfo("operation results in numeric out-of-bounds", sinfo, undefined);

        if(oprtype === "Int") {
            return `_$rc_i(${this.emitExpression(lhs, true)} ${op} ${this.emitExpression(rhs, true)}, ${eemsg})`;
        }
        else if(oprtype === "Nat") {
            return `_$rc_n(${this.emitExpression(lhs, true)} ${op} ${this.emitExpression(rhs, true)}, ${eemsg})`;
        }
        else if(oprtype === "BigInt") {
            const eexp = `${this.emitExpression(lhs, false)} ${op} ${this.emitExpression(rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else if(oprtype === "BigNat") {
            return `_$rc_N(${this.emitExpression(lhs, true)} ${op} ${this.emitExpression(rhs, true)}, ${eemsg})`;
        }
        else if(oprtype === "Float") {
            return `_$rc_f(${this.emitExpression(lhs, true)} ${op} ${this.emitExpression(rhs, true)}, ${eemsg})`;
        }
        else {
            assert(false, "Unknown bin opr type");
        }
    }

    private emitBinAddExpression(exp: BinAddExpression, toplevel: boolean): string {
        return this.emitBinOpratorExpression(exp.sinfo, exp.lhs, exp.rhs, (exp.opertype as TypeSignature).tkeystr, "+", toplevel);
    }

    private emitBinSubExpression(exp: BinSubExpression, toplevel: boolean): string {
        return this.emitBinOpratorExpression(exp.sinfo, exp.lhs, exp.rhs, (exp.opertype as TypeSignature).tkeystr, "-", toplevel);
    }
    
    private emitBinMultExpression(exp: BinMultExpression, toplevel: boolean): string {
        return this.emitBinOpratorExpression(exp.sinfo, exp.lhs, exp.rhs, (exp.opertype as TypeSignature).tkeystr, "*", toplevel);
    }
    
    private emitBinDivExpression(exp: BinDivExpression, toplevel: boolean): string {
        const oprtype = (exp.opertype as TypeSignature).tkeystr;
        const eemsg = this.getErrorInfo("division by zero", exp.sinfo, undefined);

        if(oprtype === "Int") {
            return `_$dc_i(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}, ${eemsg})`;
        }
        else if(oprtype === "Nat") {
            return `_$dc_n(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}, ${eemsg})`;
        }
        else if(oprtype === "BigInt") {
            return `_$dc_I(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}, ${eemsg})`;
        }
        else if(oprtype === "BigNat") {
            return `_$dc_N(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}, ${eemsg})`;
        }
        else if(oprtype === "Float") {
            return `_$dc_f(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)}, ${eemsg})`;
        }
        else {
            assert(false, "Unknown bin div type");
        }
    }
    
    private emitBinKeyEqExpression(exp: BinKeyEqExpression, toplevel: boolean): string {
        const kcop = exp.operkind;

        if(kcop === "lhsnone") {
            const eexp = `${this.emitExpression(exp.rhs, false)} === null`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else if(kcop === "rhsnone") {
            const eexp = `${this.emitExpression(exp.lhs, false)} === null`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else if(kcop === "lhskeyeqoption") {
            return `${this.emitExpression(exp.rhs, false)}._$keyEqOf(${this.emitExpression(exp.lhs, true)})`;
        }
        else if(kcop === "rhskeyeqoption") {
            return `${this.emitExpression(exp.lhs, false)}._$keyEqOf(${this.emitExpression(exp.rhs, true)})`;
        }
        else if(kcop === "stricteq") {
            const eexp = `${this.emitExpression(exp.lhs, false)} === ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitBinKeyNeqExpression(exp: BinKeyNeqExpression, toplevel: boolean): string {
        const kcop = exp.operkind;

        if(kcop === "lhsnone") {
            const eexp = `${this.emitExpression(exp.rhs, false)} !== null`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else if(kcop === "rhsnone") {
            const eexp = `${this.emitExpression(exp.lhs, false)} !== null`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else if(kcop === "lhskeyeqoption") {
            return `${this.emitExpression(exp.rhs, false)}._$keyNeqOf(${this.emitExpression(exp.lhs, true)})`;
        }
        else if(kcop === "rhskeyeqoption") {
            return `${this.emitExpression(exp.lhs, false)}._$keyNeqOf(${this.emitExpression(exp.rhs, true)})`;
        }
        else if(kcop === "stricteq") {
            const eexp = `${this.emitExpression(exp.lhs, false)} !== ${this.emitExpression(exp.rhs, false)}`;
            return !toplevel ? `(${eexp})` : eexp;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitNumericEqExpression(exp: NumericEqExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} === ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }

    private emitNumericNeqExpression(exp: NumericNeqExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} !== ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }
    
    private emitNumericLessExpression(exp: NumericLessExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} < ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }
    
    private emitNumericLessEqExpression(exp: NumericLessEqExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} <= ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }
    
    private emitNumericGreaterExpression(exp: NumericGreaterExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} > ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }

    private emitNumericGreaterEqExpression(exp: NumericGreaterEqExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} >= ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }

    private emitBinLogicAndExpression(exp: BinLogicAndExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} && ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }

    private emitBinLogicOrExpression(exp: BinLogicOrExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} || ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }

    private emitBinLogicImpliesExpression(exp: BinLogicImpliesExpression, toplevel: boolean): string {
        const eeexp = `!${this.emitExpression(exp.lhs, false)} || ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eeexp})` : eeexp;
    }

    private emitBinLogicIFFExpression(exp: BinLogicIFFExpression, toplevel: boolean): string {
        const eexp = `${this.emitExpression(exp.lhs, false)} === ${this.emitExpression(exp.rhs, false)}`;
        return !toplevel ? `(${eexp})` : eexp;
    }
    
    private emitMapEntryConstructorExpression(exp: MapEntryConstructorExpression): string {
        return `[${this.emitExpression(exp.kexp, true)}, ${this.emitExpression(exp.vexp, true)}]`;
    }

    private emitIfExpression(exp: IfExpression, toplevel: boolean): string {
        const texp = this.emitBUAsNeeded(this.emitExpression(exp.trueValue, false), exp.trueValue.getType(), exp.getType());
        const fexp = this.emitBUAsNeeded(this.emitExpression(exp.falseValue, false), exp.falseValue.getType(), exp.getType());

        if(exp.test.itestopt === undefined) {
            const eexp = `${this.emitExpression(exp.test.exp, false)} ? ${texp} : ${fexp}`;
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
                this.bindernames.add(exp.binder.scopename);

                const ttest = this.processITestAsTest(vval, exp.test.exp.getType(), exp.test.itestopt);
                const tbindexp = this.emitBUAsNeeded(vval, exp.test.exp.getType(), exp.trueBindType as TypeSignature);
                const fbindexp = this.emitBUAsNeeded(vval, exp.test.exp.getType(), exp.falseBindType as TypeSignature);
                const eexp = `${ttest} ? (${exp.binder.scopename} = ${tbindexp}, ${texp}) : (${exp.binder.scopename} = ${fbindexp}, ${fexp})`;
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
                return this.emitParseAsTypeExpression(exp as ParseAsTypeExpression);
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

    private emitCallRefThisExpression(exp: CallRefThisExpression): string {
        assert(false, "Not implemented -- CallRefThis");
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
        switch (ttag) {
            case ExpressionTag.CallRefThisExpression: {
                return this.emitCallRefThisExpression(exp as CallRefThisExpression);
            }
            case ExpressionTag.CallRefSelfExpression: {
                return this.emitCallRefSelfExpression(exp as CallRefSelfExpression);
            }
            case ExpressionTag.CallTaskActionExpression: {
                return this.emitCallTaskActionExpression(exp as CallTaskActionExpression);
            }
            case ExpressionTag.TaskRunExpression: {
                return this.emitTaskRunExpression(exp as TaskRunExpression);
            }
            case ExpressionTag.TaskMultiExpression: {
                return this.emitTaskMultiExpression(exp as TaskMultiExpression);
            }
            case ExpressionTag.TaskDashExpression: {
                return this.emitTaskDashExpression(exp as TaskDashExpression);
            }
            case ExpressionTag.TaskAllExpression: {
                return this.emitTaskAllExpression(exp as TaskAllExpression);
            }
            case ExpressionTag.TaskRaceExpression: {
                return this.emitTaskRaceExpression(exp as TaskRaceExpression);
            }
            default: {
                return this.emitExpression(exp, true);
            }
        }
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
        //TODO: we will need to fix this up when RHS can do stuff like ref updates and early exits (can't just cast on this if it does)
        const rhsexp = this.emitBUAsNeeded(this.emitExpressionRHS(stmt.exp), stmt.exp.getType(), stmt.actualtype as TypeSignature);
        
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

            //TODO: we will need to fix this up when RHS can do stuff like ref updates and early exits (can't just assign on this if it does)
            return `${stmt.isConst ? "const": "let"} [${idecls.join(", ")}] = ${eexp};`;
        }
        else {
            //TODO: need to check if there are deps between the defs and uses in the expressions here!!!
            
            const eexps = stmt.exp.map((ee, ii) => this.emitBUAsNeeded(this.emitExpression(ee, true), ee.getType(), stmt.actualtypes[ii]));
            const idecls = stmt.decls.map((dd, ii) => `${dd.name} = ${eexps[ii]}`);

            return `${stmt.isConst ? "const": "let"} ${idecls.join(", ")};`;

        }
    }

    private emitVariableAssignmentStatement(stmt: VariableAssignmentStatement): string {
        //TODO: we will need to fix this up when RHS can do stuff like ref updates and early exits (can't just assign on this if it does)
        const rhsexp = this.emitBUAsNeeded(this.emitExpressionRHS(stmt.exp), stmt.exp.getType(), stmt.vtype as TypeSignature);

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

            //TODO: we will need to fix this up when RHS can do stuff like ref updates and early exits (can't just assign on this if it does)
            return `[${names.join(", ")}] = ${eexp};`;
        }
        else {
            const eexps = stmt.exp.map((ee, ii) => this.emitBUAsNeeded(this.emitExpression(ee, true), ee.getType(), stmt.vtypes[ii]));

            return `${stmt.names.map((nn, ii) => `${nn} = ${eexps[ii]}`).join(", ")};`;            
        }
    }

    private emitVariableRetypeStatement(stmt: VariableRetypeStatement): string {
        assert("Not Implemented -- emitVariableRetypeStatement");

        //TODO: add type check assertion
        return "";
    }

    private emitReturnVoidStatement(stmt: ReturnVoidStatement): string {
        if(this.returncompletecall === undefined) {
            return "return;";
        }
        else {
            return `return ${this.returncompletecall};`;
        }
    }

    private emitReturnSingleStatement(stmt: ReturnSingleStatement): string {
        //TODO: we will need to fix this up when RHS can do stuff like ref updates and early exits (can't just return on this if it does)
        const rexp = this.emitExpressionRHS(stmt.value);

        if(this.returncompletecall === undefined) {
            return `return ${rexp};`;
        }
        else {
            return `return ${this.returncompletecall.replace("$[RESULT ARG]$", this.emitExpressionRHS(stmt.value))};`;
        }
    }

    private emitReturnMultiStatement(stmt: ReturnMultiStatement): string {
        const rexp = `[stmt.value.map((vv, ii) => this.emitBUAsNeeded(this.emitExpression(vv, true), vv.getType(), stmt.rtypes[ii])).join(", ")}]`;

        if(this.returncompletecall === undefined) {
            return `return ${rexp};`;
        }
        else {
            return `return ${this.returncompletecall.replace("$[RESULT ARG]$", rexp)};`;
        }
    }

    private emitIfStatement(stmt: IfStatement, fmt: JSCodeFormatter): string {
        if(stmt.cond.itestopt === undefined) {
            const test = this.emitExpression(stmt.cond.exp, true);
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

                fmt.indentPush();
                const body = this.emitBlockStatement(stmt.trueBlock, fmt);
                const bassign = fmt.indent(`let ${stmt.binder.scopename} = ${this.emitBUAsNeeded(vexp, stmt.cond.exp.getType(), stmt.trueBindType as TypeSignature)};`) + " " + body + "\n";
                fmt.indentPop();

                return `if(${test}) {\n${bassign}${fmt.indent("}")}`;
            }
        }
    }

    private emitIfElseStatement(stmt: IfElseStatement, fmt: JSCodeFormatter): string {
        if(stmt.cond.itestopt === undefined) {
            const test = this.emitExpression(stmt.cond.exp, true);
            const tbody = this.emitBlockStatement(stmt.trueBlock, fmt);
            const fbody = this.emitBlockStatement(stmt.falseBlock, fmt);

            return `if(${test}) ${tbody}\n${fmt.indent("")}else ${fbody}`;
        }
        else {
            if(stmt.binder === undefined) {
                const test = this.processITestAsTest(this.emitExpression(stmt.cond.exp, true), stmt.cond.exp.getType(), stmt.cond.itestopt);
                const tbody = this.emitBlockStatement(stmt.trueBlock, fmt);
                const fbody = this.emitBlockStatement(stmt.falseBlock, fmt);

                return `if(${test}) ${tbody}\n${fmt.indent("")}else ${fbody}`;
            }
            else {
                const vexp = this.emitExpression(stmt.cond.exp, false);
                const test = this.processITestAsTest(vexp, stmt.cond.exp.getType(), stmt.cond.itestopt);

                fmt.indentPush();
                const tbody = this.emitBlockStatement(stmt.trueBlock, fmt);
                const tbassign = fmt.indent(`let ${stmt.binder.scopename} = ${this.emitBUAsNeeded(vexp, stmt.cond.exp.getType(), stmt.trueBindType as TypeSignature)};`) + " " + tbody + "\n";

                const fbody = this.emitBlockStatement(stmt.falseBlock, fmt);
                const fbassign = fmt.indent(`let ${stmt.binder.scopename} = ${this.emitBUAsNeeded(vexp, stmt.cond.exp.getType(), stmt.falseBindType as TypeSignature)};`) + " " + fbody + "\n";
                fmt.indentPop();

                return `if(${test}) {\n${tbassign}${fmt.indent("}")}\n${fmt.indent("else {")}\n${fbassign}${fmt.indent("}")}`;
            }
        }
    }

    private emitIfElifElseStatement(stmt: IfElifElseStatement, fmt: JSCodeFormatter): string {
        assert(false, "Not implemented -- IfElifElse");
    }

    private emitSwitchStatement(stmt: SwitchStatement, fmt: JSCodeFormatter): string {
        assert(false, "Not implemented -- Switch");
    }

    private emitMatchStatement(stmt: MatchStatement, fmt: JSCodeFormatter): string {
        assert(false, "Not implemented -- Match");
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
        return `try { console.log("_debug>> " + ${this.emitExpression(stmt.value, true)}); } catch { console.log("Error evaluating debug statement @ ${this.currentfile}:${stmt.sinfo.line}"); }`;
    }

    private emitVoidRefCallStatement(stmt: VoidRefCallStatement): string {
        assert(false, "Not implemented -- VoidRefCall");
    }

    private emitVarUpdateStatement(stmt: VarUpdateStatement): string {
        assert(false, "Not implemented -- VarUpdate");
    }

    private emitThisUpdateStatement(stmt: ThisUpdateStatement): string {
        assert(false, "Not implemented -- ThisUpdate");
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
                stmtstrs.push("\n");
            }
            else {
                const stag = stmti.tag;
                switch(stag) {
                    case StatementTag.BlockStatement: {
                        if(!prevskip) {
                            stmtstrs.push("\n");
                        }
                        stmtstrs.push(sstr);
                        stmtstrs.push("\n");
                        prevskip = true;
                        break;
                    }
                    case StatementTag.IfStatement:
                    case StatementTag.IfElseStatement: 
                    case StatementTag.IfElifElseStatement:
                    case StatementTag.SwitchStatement:
                    case StatementTag.MatchStatement: {
                        if(!prevskip) {
                            stmtstrs.push("\n");
                        }
                        stmtstrs.push(sstr);
                        stmtstrs.push("\n");
                        prevskip = true;
                        break;
                    }
                    default: {
                        stmtstrs.push(sstr);
                        prevskip = false;
                    }
                }
                stmtstrs.push("\n");
            }
        }
        fmt.indentPop();

        return stmtstrs;
    }

    private emitBlockStatement(stmt: BlockStatement, fmt: JSCodeFormatter): string {
        const stmts = this.emitStatementArray(stmt.statements, fmt);

        return ["{\n", ...stmts, fmt.indent("}")].join("");
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

    private emitBodyImplementation(body: BodyImplementation, returntype: TypeSignature, initializers: string[], preconds: string[], refsaves: string[], returncompletecall: string | undefined, fmt: JSCodeFormatter): string | undefined {
        if(body instanceof AbstractBodyImplementation || body instanceof PredicateUFBodyImplementation) {
            return undefined;
        }

        if(body instanceof BuiltinBodyImplementation) {
            assert(false, "Not implemented -- emitBuiltinBodyImplementation");
        }
        else if(body instanceof SynthesisBodyImplementation) {
            assert(false, "Not implemented -- emitSynthesisBodyImplementation");
        }
        else {
            let stmts: string[] = [];
            if(body instanceof ExpressionBodyImplementation) {
                fmt.indentPush();
                stmts.push(fmt.indent(`return ${this.emitBUAsNeeded(this.emitExpression(body.exp, true), body.exp.getType(), returntype)};`));
                fmt.indentPop();
            }
            else {
                assert(body instanceof StandardBodyImplementation);
                
                this.returncompletecall = returncompletecall;
                stmts = this.emitStatementArray(body.statements, fmt);
            }

            if(this.bindernames.size !== 0) {
                fmt.indentPush();
                const bvars = fmt.indent(`var ${[...this.bindernames].join(", ")};\n\n`);
                fmt.indentPop();

                stmts = [bvars, ...stmts];
            }

            if(initializers.length === 0 && preconds.length === 0 && refsaves.length === 0) {
                return ["{\n", ...stmts, fmt.indent("}")].join("");
            }
            else {
                return ["{\n", ...(initializers || []), ...(preconds || []), ...(refsaves || []), ...stmts, fmt.indent("}")].join("");
            }
        }
    }

    private emitParameterInitializers(params: InvokeParameterDecl[]): string[] {
        //TODO: we need to compute the dependency order here and check for cycles later

        let inits: string[] = [];
        for(let i = 0; i < params.length; ++i) {
            const p = params[i];
            
            if(p.optDefaultValue !== undefined) {
                inits.push(`if(${p.name} === undefined) { ${p.name} = ${this.emitExpression(p.optDefaultValue.exp, true)}; }`);
            }
        }

        return inits;
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
                refsaves.push(`const $${p.name} = ${p.name};`);
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

                invexps.push(`${chkcall}: (${args}) => ${body}`);
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

            vexps.push(`${chkcall}: (${args}) => ${body}`);
        }

        return vexps;
    }

    private emitExamplesInline(sinfo: SourceInfo, args: TypeSignature[], resulttype: TypeSignature, example: InvokeExampleDeclInline): string[] {
        assert(false, "This should be checked as a BSQON value"); //maybe in a secondary pass
    }

    private emitExamplesFiles(sinfo: SourceInfo, args: TypeSignature[], resulttype: TypeSignature, example: InvokeExampleDeclFile): string[] {
        assert(false, "Not implemented -- checkExamplesFiles"); //We probably don't want to load the contents here -- but maybe as a separate pass????
    }

    private emitExamples(sinfo: SourceInfo, args: TypeSignature[], resulttype: TypeSignature, examples: InvokeExample[]): string[] {
        let exinfo: string[] = [];
        if(this.generateTestInfo) {
            for(let i = 0; i < examples.length; ++i) {
                const ex = examples[i];
                if(ex instanceof InvokeExampleDeclInline) {
                    const inlinetests = this.emitExamplesInline(sinfo, args, resulttype, ex);
                    exinfo.push(...inlinetests);
                }
                else {
                    assert(ex instanceof InvokeExampleDeclFile);
                    const filetests = this.emitExamplesFiles(sinfo, args, resulttype, ex);
                    exinfo.push(...filetests);
                }
            }
        }

        return exinfo;
    }

    private emitExplicitInvokeFunctionDeclSignature(idecl: FunctionInvokeDecl): string {
        return `(${idecl.params.map((p) => p.name).join(", ")})`;
    }

    private checkExplicitFunctionInvokeDeclMetaData(idecl: FunctionInvokeDecl, inits: string[], preconds: string[], refsaves: string[], tests: string[]): string[] {
        inits.push(...this.emitParameterInitializers(idecl.params));
        preconds.push(...this.emitRequires(idecl.preconditions));
        refsaves.push(...this.emitRefSaves(idecl.params));

        tests.push(...this.emitExamples(idecl.sinfo, idecl.params.map((p) => p.type), idecl.resultType, idecl.examples));

        return this.emitEnsures(idecl.postconditions);
    }

    private emitFunctionDecl(fdecl: FunctionInvokeDecl, optenclosingtype: NominalTypeSignature | undefined,  optmapping: TemplateNameMapper | undefined, fmt: JSCodeFormatter): {body: string, resfimpl: string | undefined, tests: string[]} {
        if(optmapping !== undefined) {
            this.mapper = optmapping;
        }

        const sig = this.emitExplicitInvokeFunctionDeclSignature(fdecl);

        let initializers: string[] = [];
        let preconds: string[] = [];
        let refsaves: string[] = [];
        let tests: string[] = [];
        const ensures = this.checkExplicitFunctionInvokeDeclMetaData(fdecl, initializers, preconds, refsaves, tests);

        let resf: string | undefined = undefined;
        let resfimpl: string | undefined = undefined;
        if(ensures.length !== 0) {
            //TODO: we will need to handle ref params here too
            assert(fdecl.params.every((p) => !p.isRefParam), "Not implemented -- checkEnsuresRefParams");

            const resb = ensures.map((e) => fmt.indent(e)).join("\n");

            let [resf, rss] = fdecl instanceof NamespaceFunctionDecl ? EmitNameManager.generateOnCompleteDeclarationNameForNamespaceFunction(this.getCurrentNamespace(), fdecl as NamespaceFunctionDecl, optmapping) : [EmitNameManager.generateOnCompleteDeclarationNameForTypeFunction(optenclosingtype as NominalTypeSignature, fdecl as TypeFunctionDecl, optmapping), true];
            resfimpl = `${resf}(${fdecl.params.map((p) => p.name).join(", ")}, $return)${rss ? " => " : " "}{\n${resb}${fmt.indent("\n")}}`;
        }

        const body = this.emitBodyImplementation(fdecl.body, fdecl.resultType, initializers, preconds, refsaves, resf, fmt);
        this.mapper = undefined;

        const [nf, nss] = fdecl instanceof NamespaceFunctionDecl ? EmitNameManager.generateDeclarationNameForNamespaceFunction(this.getCurrentNamespace(), fdecl as NamespaceFunctionDecl, optmapping) : [EmitNameManager.generateAccssorNameForTypeFunction(this.getCurrentNamespace(), optenclosingtype as NominalTypeSignature, fdecl as TypeFunctionDecl, optmapping), true];
        return {body: `${nf}${sig}${nss ? " => " : " "}${body}`, resfimpl: resfimpl, tests: tests};
    }

    private emitFunctionDecls(optenclosingtype: NominalTypeSignature | undefined, fdecls: [FunctionInvokeDecl, FunctionInstantiationInfo | undefined][], fmt: JSCodeFormatter): {decls: string[], tests: string[]} {
        let decls: string[] = [];
        let tests: string[] = [];

        for(let i = 0; i < fdecls.length; ++i) {
            const fdecl = fdecls[i][0];
            const fii = fdecls[i][1]; 
    
            this.currentfile = fdecl.file;

            if(fii !== undefined) {
                if(fii.binds === undefined) {
                    const {body, resfimpl, tests} = this.emitFunctionDecl(fdecl, optenclosingtype, undefined, fmt);
            
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
                        const {body, resfimpl, tests} = this.emitFunctionDecl(fdecl, optenclosingtype, fii.binds[j], fmt);
            
                        if(resfimpl !== undefined) {
                            idecls.push(resfimpl);
                        }
                        idecls.push(body);

                        tests.push(...tests);
                    }
                    fmt.indentPop();

                    const fobj = `${fdecl.name}: {\n${idecls.map((dd) => fmt.indent(dd)).join(", ")}${fmt.indent("}")}`;
                    decls.push(fobj);
                }
            }
        }

        return {decls: decls, tests: tests};
    }

    private emitMethodDecls(rcvr: TypeSignature, mdecls: [MethodDecl, MethodInstantiationInfo | undefined][], fmt: JSCodeFormatter): {decls: string[], tests: string[]} {
        let decls: string[] = [];
        let tests: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {
            const mdecl = mdecls[i][0];
            const mii = mdecls[i][1];

            this.currentfile = mdecl.file;

            if(mii !== undefined) {
                assert(false, "Not implemented -- checkMethodDecl");
            }
        }

        return {decls: decls, tests: tests};
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
            const lexp = `() => ${eexp}`;

            cdecls.push(`${m.name}: () => _$memoconstval(this._$consts, "${m.name}", ${lexp})`);
        }

        if(cdecls.length !== 0) {
            cdecls = ["_$consts: new JSMap()", ...cdecls];
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
                const args = ""; //tdecl.saturatedBFieldInfo.map((fi) => "$" + fi.name).join(", "); --------- TODO: we need to compute dependencies and cycles

                const body = this.emitExpression(m.defaultValue.exp, true);
                initializers.push(`${chkcall}: (${args}) => ${body}`);
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
        return `$tsym: Symbol.for("${rcvr.tkeystr}")`;
    }

    private emitVTable(tdecl: AbstractNominalTypeDecl, fmt: JSCodeFormatter): string {
        return "[VTABLE -- NOT IMPLEMENTED]";
    }

    private emitCreate(tdecl: AbstractNominalTypeDecl, fmt: JSCodeFormatter): string {
        const ddecls = tdecl.saturatedBFieldInfo.filter((fi) => fi.hasdefault).
            map((fi) => `if(${fi.name} === undefined) { ${fi.name} = ${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(fi.containingtype) as NominalTypeSignature, `$default$${fi.name}`)}(); }`);
        
        let rechks: string[] = [];
        if(tdecl instanceof TypedeclTypeDecl && tdecl.optofexp !== undefined) {
            if(tdecl.optofexp.exp.tag === ExpressionTag.LiteralUnicodeRegexExpression) {
                rechks.push(`_$formatchk(_$accepts(${this.emitLiteralUnicodeRegexExpression(tdecl.optofexp.exp as LiteralRegexExpression)}, $value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex", tdecl.optofexp.exp.sinfo, undefined)});`);
            }
            else if(tdecl.optofexp.exp.tag === ExpressionTag.LiteralCRegexExpression) {
                rechks.push(`_$formatchk(_$accepts(${this.emitLiteralCRegexExpression(tdecl.optofexp.exp as LiteralRegexExpression)}, $value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex", tdecl.optofexp.exp.sinfo, undefined)});`);
            }
            else {
                const nsaccess = this.emitAccessNamespaceConstantExpression(tdecl.optofexp.exp as AccessNamespaceConstantExpression);
                const retag = `'${(tdecl.optofexp.exp as AccessNamespaceConstantExpression).ns.ns.join("::")}::${(tdecl.optofexp.exp as AccessNamespaceConstantExpression).name}'`;
                rechks.push(`_$formatchk(_$accepts(${nsaccess}, $value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex -- " + (tdecl.optofexp.exp as AccessNamespaceConstantExpression).name, tdecl.optofexp.exp.sinfo, retag)});`);
            }
        }

        const cchks = tdecl.allInvariants.map((inv) => {
            const chkcall = `${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(inv.containingtype) as NominalTypeSignature, `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`)}`;
            const args = (tdecl instanceof TypedeclTypeDecl) ? "$value" : inv.containingtype.decl.saturatedBFieldInfo.map((fi) => fi.name).join(", ");
            const info = this.getErrorInfo("failed invariant", inv.sinfo, inv.tag);

            return `_$invariant(${chkcall}(${args}), ${info});`
        });

        const ccons = (tdecl instanceof TypedeclTypeDecl) ? "return $value;" : `return { ${tdecl.saturatedBFieldInfo.map((fi) => fi.name + ": " + fi.name).join(", ")} };`;

        fmt.indentPush();
        const bbody = [...ddecls, ...rechks, ...cchks, ccons].map((ee) => fmt.indent(ee)).join("\n");
        fmt.indentPop();

        return `$create: (${(tdecl instanceof TypedeclTypeDecl) ? "$value" : tdecl.saturatedBFieldInfo.map((fi) => fi.name).join(", ")}) => {\n${bbody}\n${fmt.indent("}")}`;
    }

    private emitCreateAPIValidate(tdecl: AbstractNominalTypeDecl, fmt: JSCodeFormatter): string {
        const ddecls = tdecl.saturatedBFieldInfo.filter((fi) => fi.hasdefault).
            map((fi) => `if(${fi.name} === undefined) { ${fi.name} = ${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(fi.containingtype) as NominalTypeSignature, `$default$${fi.name}`)}(); }`);
        
        let rechks: string[] = [];
        if(tdecl instanceof TypedeclTypeDecl && tdecl.optofexp !== undefined) {
            if(tdecl.optofexp.exp.tag === ExpressionTag.LiteralUnicodeRegexExpression) {
                rechks.push(`_$formatchk(_$accepts(${this.emitLiteralUnicodeRegexExpression(tdecl.optofexp.exp as LiteralRegexExpression)}, $value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex", tdecl.optofexp.exp.sinfo, undefined)});`);
            }
            else if(tdecl.optofexp.exp.tag === ExpressionTag.LiteralCRegexExpression) {
                rechks.push(`_$formatchk(_$accepts(${this.emitLiteralCRegexExpression(tdecl.optofexp.exp as LiteralRegexExpression)}, $value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex", tdecl.optofexp.exp.sinfo, undefined)});`);
            }
            else {
                const nsaccess = this.emitAccessNamespaceConstantExpression(tdecl.optofexp.exp as AccessNamespaceConstantExpression);
                const retag = `'${(tdecl.optofexp.exp as AccessNamespaceConstantExpression).ns.ns.join("::")}::${(tdecl.optofexp.exp as AccessNamespaceConstantExpression).name}'`;
                rechks.push(`_$formatchk(_$accepts(${nsaccess}, $value, ${this.getCurrentINNS()}), ${this.getErrorInfo("failed regex -- " + (tdecl.optofexp.exp as AccessNamespaceConstantExpression).name, tdecl.optofexp.exp.sinfo, retag)});`);
            }
        }

        const cchks = tdecl.allInvariants.map((inv) => {
            const chkcall = `${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(inv.containingtype) as NominalTypeSignature, `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`)}`;
            const args = (tdecl instanceof TypedeclTypeDecl) ? "$value" : inv.containingtype.decl.saturatedBFieldInfo.map((fi) => fi.name).join(", ");
            const info = this.getErrorInfo("failed invariant", inv.sinfo, inv.tag);

            return `_$invariant(${chkcall}(${args}), ${info});`
        });

        const vchks = tdecl.allValidates.map((inv) => {
            const chkcall = `${EmitNameManager.generateAccessorForTypeSpecialName(this.currentns as NamespaceDeclaration, this.tproc(inv.containingtype) as NominalTypeSignature, `$checkinv_${inv.sinfo.line}_${inv.sinfo.pos}`)}`;
            const args = (tdecl instanceof TypedeclTypeDecl) ? "$value" : inv.containingtype.decl.saturatedBFieldInfo.map((fi) => fi.name).join(", ");
            const info = this.getErrorInfo("failed validation", inv.sinfo, inv.tag);

            return `_$validate(${chkcall}(${args}), ${info});`
        });

        const ccons = (tdecl instanceof TypedeclTypeDecl) ? "return $value;" : `return { ${tdecl.saturatedBFieldInfo.map((fi) => fi.name + ": " + fi.name).join(", ")} };`;

        fmt.indentPush();``
        const bbody = [...ddecls, ...rechks, ...cchks, ...vchks, ccons].map((ee) => fmt.indent(ee)).join("\n");
        fmt.indentPop();

        return `$createAPI: (${(tdecl instanceof TypedeclTypeDecl) ? "$value" : tdecl.saturatedBFieldInfo.map((fi) => fi.name).join(", ")}) => {\n${bbody}\n${fmt.indent("}")}`;
    }

    private emitStdTypeDeclHelper(tdecl: AbstractNominalTypeDecl, rcvr: NominalTypeSignature, optfdecls: MemberFieldDecl[] | undefined, instantiation: TypeInstantiationInfo, isentity: boolean, fmt: JSCodeFormatter): {decls: string[], tests: string[]} {
        if(tdecl.terms.length !== 0) {
            this.mapper = instantiation.binds;
        }

        fmt.indentPush();
        let decls: string[] = [];
        let tests: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));
        if(optfdecls !== undefined) {
            decls.push(...this.emitMemberFieldInitializers(tdecl, optfdecls, fmt));
        }

        //make sure all of the invariants on this typecheck
        decls.push(...this.emitInvariants(rcvr, tdecl.saturatedBFieldInfo, tdecl.invariants));
        decls.push(...this.emitValidates(rcvr, tdecl.saturatedBFieldInfo, tdecl.validates));
        
        if(isentity) {
            if(optfdecls || tdecl.allInvariants.length !== 0) {
                decls.push(this.emitCreate(tdecl, fmt));
            }

            if(optfdecls || tdecl.allInvariants.length !== 0 || tdecl.validates.length !== 0) {
                decls.push(this.emitCreateAPIValidate(tdecl, fmt));
            }
        }

        decls.push(...this.emitConstMemberDecls(tdecl.consts));

        const fdecls = this.emitFunctionDecls(rcvr, tdecl.functions.map((fd) => [fd, instantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls.decls);
        tests.push(...fdecls.tests);

        const mdecls = this.emitMethodDecls(rcvr, tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls.decls);
        tests.push(...mdecls.tests);

        if(isentity) {
            if(tdecl.hasDynamicInvokes) {
                decls.push(this.emitVTable(tdecl, fmt));
            }
        }

        this.mapper = undefined;
        fmt.indentPop();

        return {decls: decls, tests: tests};
    }

    private emitInteralSimpleTypeDeclHelper(tdecl: InternalEntityTypeDecl, rcvr: NominalTypeSignature, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter, extradecls: string[], nested: string | undefined): string {
        if(tdecl.terms.length !== 0) {
            this.mapper = instantiation.binds;
        }

        fmt.indentPush();
        let decls: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        decls.push(...this.emitConstMemberDecls(tdecl.consts));

        const fdecls = this.emitFunctionDecls(rcvr, tdecl.functions.map((fd) => [fd, instantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls.decls);

        const mdecls = this.emitMethodDecls(rcvr, tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls.decls);

        const declsentry = [...decls, ...extradecls].map((dd) => fmt.indent(dd)).join(",\n");

        this.mapper = undefined;
        fmt.indentPop();

        const obj = `{\n${declsentry}\n${fmt.indent("}")}`;

        if(nested !== undefined) {
            return `${tdecl.name}: ${obj}`;
        }
        else {
            if(tdecl.terms.length !== 0) {
                return `${tdecl.name}[${EmitNameManager.emitTypeTermKey(rcvr)}] = ${obj}`;
            }
            else {
                return `export const ${tdecl.name} = ${obj}`;
            }
        }
    }

    private emitPrimitiveEntityTypeDecl(ns: NamespaceDeclaration, tdecl: PrimitiveEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitEnumTypeDecl(ns: NamespaceDeclaration, tdecl: EnumTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        fmt.indentPush();
        let decls: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        const mdecls = this.emitMethodDecls(rcvr, tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls.decls);

        decls.push(...tdecl.members.map((mm) => `${mm}: Symbol(${mm})`));

        if(tdecl.hasDynamicInvokes) {
            decls.push(this.emitVTable(tdecl, fmt));
        }

        const declsentry = [...decls].map((dd) => fmt.indent(dd)).join(",\n");

        fmt.indentPop();

        const obj = `{\n${declsentry}\n${fmt.indent("}")}`;

        return {decl: `export const ${tdecl.name} = ${obj}`, tests: mdecls.tests};
    }

    private emitTypedeclTypeDecl(ns: NamespaceDeclaration, tdecl: TypedeclTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);

        fmt.indentPush();
        let decls: string[] = [];
        let tests: string[] = [];

        decls.push(this.emitTypeSymbol(rcvr));

        //make sure all of the invariants on this typecheck
        decls.push(...this.emitInvariants(rcvr, tdecl.saturatedBFieldInfo, tdecl.invariants));
        decls.push(...this.emitValidates(rcvr, tdecl.saturatedBFieldInfo, tdecl.validates));

        if(tdecl.optofexp !== undefined || tdecl.allInvariants.length !== 0) {
            decls.push(this.emitCreate(tdecl, fmt));
        }

        if(tdecl.optofexp !== undefined || tdecl.allInvariants.length !== 0 || tdecl.validates.length !== 0) {
            decls.push(this.emitCreateAPIValidate(tdecl, fmt));
        }

        decls.push(...this.emitConstMemberDecls(tdecl.consts));

        const fdecls = this.emitFunctionDecls(rcvr, tdecl.functions.map((fd) => [fd, instantiation.functionbinds.get(fd.name)]), fmt);
        decls.push(...fdecls.decls);
        tests.push(...fdecls.tests);

        const mdecls = this.emitMethodDecls(rcvr, tdecl.methods.map((md) => [md, instantiation.methodbinds.get(md.name)]), fmt);
        decls.push(...mdecls.decls);
        tests.push(...mdecls.tests);

        if(tdecl.hasDynamicInvokes) {
            decls.push(this.emitVTable(tdecl, fmt));
        }

        const declsentry = [...decls].map((dd) => fmt.indent(dd)).join(",\n");

        fmt.indentPop();

        const obj = `{\n${declsentry}\n${fmt.indent("}")}`;

        return {decl: `export const ${tdecl.name} = ${obj}`, tests: tests};
    }

    private emitOkTypeDecl(ns: NamespaceDeclaration, tdecl: OkTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "Result");
    }

    private emitFailTypeDecl(ns: NamespaceDeclaration, tdecl: FailTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T", "E"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "Result");
    }

    private emitAPIRejectedTypeDecl(ns: NamespaceDeclaration, tdecl: APIRejectedTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "APIResult");
    }

    private emitAPIFailedTypeDecl(ns: NamespaceDeclaration, tdecl: APIFailedTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "APIResult");
    }

    private emitAPIErrorTypeDecl(ns: NamespaceDeclaration, tdecl: APIErrorTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "APIResult");
    }

    private emitAPISuccessTypeDecl(ns: NamespaceDeclaration, tdecl: APISuccessTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, ["T"]);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], "APIResult");
    }

    private emitSomeTypeDecl(ns: NamespaceDeclaration, tdecl: SomeTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitMapEntryTypeDecl(ns: NamespaceDeclaration, tdecl: MapEntryTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitListTypeDecl(ns: NamespaceDeclaration, tdecl: ListTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitStackTypeDecl(ns: NamespaceDeclaration, tdecl: StackTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitQueueTypeDecl(ns: NamespaceDeclaration, tdecl: QueueTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitSetTypeDecl(ns: NamespaceDeclaration, tdecl: SetTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitMapTypeDecl(ns: NamespaceDeclaration, tdecl: MapTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitEventListTypeDecl(ns: NamespaceDeclaration, tdecl: EventListTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitEntityTypeDecl(ns: NamespaceDeclaration, tdecl: EntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, true, fmt);
        fmt.indentPush();
        const declsfmt = rr.decls.map((dd) => fmt.indent(dd)).join(",\n");
        fmt.indentPop();

        const obj = `{\n${declsfmt}\n${fmt.indent("}")}`;

        if(tdecl.terms.length !== 0) {
            return {decl: `${tdecl.name}[${EmitNameManager.emitTypeTermKey(rcvr)}] = ${obj}`, tests: rr.tests};
        }
        else {
            return {decl: `export const ${tdecl.name} = ${obj}`, tests: rr.tests};
        }
    }

    private emitOptionTypeDecl(ns: NamespaceDeclaration, tdecl: OptionTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [], undefined);
    }

    private emitResultTypeDecl(ns: NamespaceDeclaration, tdecl: ResultTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        fmt.indentPush();
        const okdecl = this.emitOkTypeDecl(ns, tdecl.getOkType(), instantiation, fmt);
        const faildecl = this.emitFailTypeDecl(ns, tdecl.getFailType(), instantiation, fmt);
        fmt.indentPop();

        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [okdecl, faildecl], undefined);
    }

    private emitAPIResultTypeDecl(ns: NamespaceDeclaration, tdecl: APIResultTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): string {
        fmt.indentPush();
        const rejecteddecl = this.emitAPIRejectedTypeDecl(ns, tdecl.getAPIRejectedType(), instantiation, fmt);
        const faileddecl = this.emitAPIFailedTypeDecl(ns, tdecl.getAPIFailedType(), instantiation, fmt);
        const errordecl = this.emitAPIErrorTypeDecl(ns, tdecl.getAPIErrorType(), instantiation, fmt);
        const successdecl = this.emitAPISuccessTypeDecl(ns, tdecl.getAPISuccessType(), instantiation, fmt);
        fmt.indentPop();

        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        return this.emitInteralSimpleTypeDeclHelper(tdecl, rcvr, instantiation, fmt, [rejecteddecl, faileddecl, errordecl, successdecl], undefined);
    }

    private emitConceptTypeDecl(ns: NamespaceDeclaration, tdecl: ConceptTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, false, fmt);
        fmt.indentPush();
        const declsfmt = rr.decls.map((dd) => fmt.indent(dd)).join(",\n");
        fmt.indentPop();

        const obj = `{\n${declsfmt}\n${fmt.indent("}")}`;

        if(tdecl.terms.length !== 0) {
            return {decl: `${tdecl.name}[${EmitNameManager.emitTypeTermKey(rcvr)}] = ${obj}`, tests: rr.tests};
        }
        else {
            return {decl: `export const ${tdecl.name} = ${obj}`, tests: rr.tests};
        }
    }

    private emitDatatypeMemberEntityTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeMemberEntityTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, true, fmt);
        fmt.indentPush();
        const declsfmt = rr.decls.map((dd) => fmt.indent(dd)).join(",\n");
        fmt.indentPop();

        const obj = `{\n${declsfmt}\n${fmt.indent("}")}`;

        if(tdecl.terms.length !== 0) {
            return {decl: `${tdecl.name}[${EmitNameManager.emitTypeTermKey(rcvr)}] = ${obj}`, tests: rr.tests};
        }
        else {
            return {decl: `export const ${tdecl.name} = ${obj}`, tests: rr.tests};
        }
    }

    private emitDatatypeTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeTypeDecl, instantiation: TypeInstantiationInfo, fmt: JSCodeFormatter): {decl: string, tests: string[]} {
        const rcvr = JSEmitter.generateRcvrForNominalAndBinds(tdecl, instantiation.binds, undefined);
        
        const rr = this.emitStdTypeDeclHelper(tdecl, rcvr, tdecl.fields, instantiation, false, fmt);
        fmt.indentPush();
        const declsfmt = rr.decls.map((dd) => fmt.indent(dd)).join(",\n");
        fmt.indentPop();

        const obj = `{\n${declsfmt}\n${fmt.indent("}")}`;

        if(tdecl.terms.length !== 0) {
            return {decl: `${tdecl.name}[${EmitNameManager.emitTypeTermKey(rcvr)}] = ${obj}`, tests: rr.tests};
        }
        else {
            return {decl: `export const ${tdecl.name} = ${obj}`, tests: rr.tests};
        }
    }

    private emitAPIDecls(ns: NamespaceDeclaration, adecls: APIDecl[]): string[] {
        if(adecls.length !== 0) {
            assert(false, "Not implemented -- checkAPIDecl");
        }

        return [];
    }

    private emitTaskDecls(ns: NamespaceDeclaration, tdecls: TaskDecl[]): string[] {
        if(tdecls.length !== 0) {
            assert(false, "Not implemented -- checkTaskDecl");
        }

        return [];
    }

    private emitNamespaceConstDecls(decls: NamespaceConstDecl[]): string[] {
        let cdecls: string[] = [];
        for(let i = 0; i < decls.length; ++i) {
            const m = decls[i];

            this.currentfile = m.file;
            const eexp = this.emitExpression(m.value.exp, true);
            const lexp = `() => ${eexp}`;

            cdecls.push(`export function ${m.name}() { return _$memoconstval(_$consts, "${m.name}", ${lexp}); }`);
        }

        if(cdecls.length !== 0) {
            cdecls = ["let _$consts = new JSMap();", ...cdecls];
        }

        return cdecls;
    }


    private emitTypeSubtypeRelation(tdecl: AbstractNominalTypeDecl, instantiation: TypeInstantiationInfo): string {
        this.mapper = instantiation.binds;
        const supers = tdecl.saturatedProvides.map((ss) => `Symbol.for("${this.tproc(ss).tkeystr}")`).join(", ");
        this.mapper = undefined;

        return `_$supertypes[Symbol.for("${instantiation.tkey}")] = [${supers}];`;
    }

    private emitNamespaceTypeDecls(ns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl[], asminstantiation: NamespaceInstantiationInfo, fmt: JSCodeFormatter): {decls: string[], supers: string[], tests: string[]} {
        let ttdecls: string[] = [];
        let alldecls: string[] = [];
        let allsupertypes: string[] = [];
        let alltests: string[] = [];

        let emittedtdecls = new Set<string>();
        for(let i = 0; i < tdecl.length; ++i) {
            const tt = tdecl[i];
            const iinsts = asminstantiation.typebinds.get(tt.name);
            if(iinsts === undefined) {
                continue;
            }

            this.currentfile = tt.file;

            if(!emittedtdecls.has(tt.name) && iinsts.some((ii) => ii.binds !== undefined)) {
                ttdecls.push(`export const ${tt.name} = {};`);

                emittedtdecls.add(tt.name);
            }

            let ddecls: string[] = [];
            for(let j = 0; j < iinsts.length; ++j) {
                const instantiation = iinsts[j];

                if(tt instanceof EnumTypeDecl) {
                    const {decl, tests} = this.emitEnumTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                    alltests.push(...tests);
                }
                else if(tt instanceof TypedeclTypeDecl) {
                    const {decl, tests} = this.emitTypedeclTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                    alltests.push(...tests);
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
                    const {decl, tests} = this.emitEntityTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                    alltests.push(...tests);
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
                    const {decl, tests} = this.emitConceptTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                    alltests.push(...tests);
                }
                else if(tt instanceof DatatypeMemberEntityTypeDecl) {
                    const {decl, tests} = this.emitDatatypeMemberEntityTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                    alltests.push(...tests);
                }
                else if(tt instanceof DatatypeTypeDecl) {
                    const {decl, tests} = this.emitDatatypeTypeDecl(ns, tt, instantiation, fmt);
                    ddecls.push(decl);
                    alltests.push(...tests);
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
            }

            if(ddecls.length === 1) {
                alldecls.push(fmt.indent(ddecls[0] + ";"));
            }
            else {
                alldecls.push(`export const ${tt.name} = {\n${ddecls.map((dd) => fmt.indent(dd)).join(",\n")}\n${fmt.indent("}")}`);
            }
        }

        return {decls: [...ttdecls, ...alldecls], supers: allsupertypes, tests: alltests};
    }

    private emitNamespaceDeclaration(decl: NamespaceDeclaration, asminstantiation: NamespaceInstantiationInfo): {contents: string, tests: string[]} {
        //all usings should be resolved and valid so nothing to do there

        let decls: string[] = [];
        let tests: string[] = [];

        const cdecls = this.emitNamespaceConstDecls(decl.consts);
        decls.push(...cdecls);

        const fdecls = this.emitFunctionDecls(undefined, decl.functions.map((fd) => [fd, asminstantiation.functionbinds.get(fd.name)]), new JSCodeFormatter(0));
        decls.push(...fdecls.decls);
        tests.push(...fdecls.tests);

        const tdecls = this.emitNamespaceTypeDecls(decl, decl.typedecls, asminstantiation, new JSCodeFormatter(0));
        decls.push(...tdecls.decls);
        tests.push(...tdecls.tests);

        const apidecls = this.emitAPIDecls(decl, decl.apis);
        decls.push(...apidecls);

        const taskdecls = this.emitTaskDecls(decl, decl.tasks);
        decls.push(...taskdecls);

        const ddecls = decls.join("\n\n");
        const supers = tdecls.supers.length !== 0 ? ("\n\n" + tdecls.supers.join("\n")) : "";

        let imports = "";
        if(decl.name !== "Core") {
            imports = `import * as $Core from "./Core.mjs";\n\n`;
        }

        let loadop = "";
        let mainop = "\n";
        if(decl.name === "Main") {

            const asmreinfo = this.assembly.toplevelNamespaces.flatMap((ns) => this.assembly.loadConstantsAndValidatorREs(ns));

            //Now process the regexs
            loadop = `\nimport { loadConstAndValidateRESystem } from "@bosque/jsbrex";\nloadConstAndValidateRESystem(${JSON.stringify(asmreinfo, undefined, 4)});`
            mainop = "\n\ntry { process.stdout.write(`${main()}\\n`); } catch(e) { process.stdout.write(`Error -- ${e.$info || e}\\n`); }\n";
        }

        return {contents: prefix + imports + ddecls + supers + loadop + mainop, tests: tests};
    }

    static emitAssembly(assembly: Assembly, mode: "release" | "testing" | "debug", buildlevel: BuildLevel, asminstantiation: NamespaceInstantiationInfo[]): [{ns: FullyQualifiedNamespace, contents: string}[], string[]] {
        const emitter = new JSEmitter(assembly, mode == "release" ? "release" : "debug", buildlevel, mode === "testing");

        //emit each of the assemblies
        let results: {ns: FullyQualifiedNamespace, contents: string}[] = [];
        let tests: string[] = [];
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            const nsdecl = assembly.toplevelNamespaces[i];
            const nsii = asminstantiation.find((ai) => ai.ns.emit() === nsdecl.fullnamespace.emit());
            
            if(nsii !== undefined) {
                emitter.currentns = nsdecl;
                const code = emitter.emitNamespaceDeclaration(nsdecl, nsii);

                results.push({ns: nsdecl.fullnamespace, contents: code.contents});
                tests.push(...code.tests);
            }
        }

        return [results, tests];
    }
}

export {
    JSEmitter
};
