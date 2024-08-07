import assert from "node:assert";

import { JSCodeFormatter, EmitNameManager } from "./jsemitter_support.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, DebugStatement, EmptyStatement, EnvironmentBracketStatement, EnvironmentUpdateStatement, Expression, ExpressionBodyImplementation, ExpressionTag, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, ITest, ITestErr, ITestNone, ITestOk, ITestSome, ITestType, LambdaInvokeExpression, LetExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTypeDeclValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PostfixProjectFromNames, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, ReturnMultiStatement, ReturnSingleStatement, ReturnVoidStatement, SelfUpdateStatement, SpecialConstructorExpression, StandardBodyImplementation, Statement, StatementTag, SwitchStatement, SynthesisBodyImplementation, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskEventEmitStatement, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, VarUpdateStatement, VoidRefCallStatement } from "../frontend/body.js";
import { AbstractCollectionTypeDecl, AbstractNominalTypeDecl, Assembly, ConstMemberDecl, ConstructableTypeDecl, EnumTypeDecl, FunctionInvokeDecl, InternalEntityTypeDecl, InvariantDecl, InvokeExample, InvokeExampleDeclFile, InvokeExampleDeclInline, InvokeParameterDecl, ListTypeDecl, MapEntryTypeDecl, MemberFieldDecl, MethodDecl, NamespaceDeclaration, NamespaceFunctionDecl, PostConditionDecl, PreConditionDecl, ResultTypeDecl, TaskActionDecl, TaskMethodDecl, TypedeclTypeDecl, TypeFunctionDecl, ValidateDecl } from "../frontend/assembly.js";
import { FullyQualifiedNamespace, NominalTypeSignature, TemplateNameMapper, TypeSignature } from "../frontend/type.js";
import { BuildLevel, CodeFormatter, isBuildLevelEnabled, SourceInfo } from "../frontend/build_decls.js";

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

    constructor(assembly: Assembly, mode: "release" | "debug", generateTestInfo: boolean) {
        this.assembly = assembly;
        this.mode = mode;
        
        this.currentfile = undefined;
        this.currentns = undefined;
    }

    private tproc(ttype: TypeSignature): TypeSignature {
        return ttype.remapTemplateBindings(this.getTemplateMapper());
    }

    private getCurrentNamespace(): NamespaceDeclaration {
        assert(this.currentns !== undefined, "Current namespace is not set");
        return this.currentns;
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
        const taccess = EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), oftype);
        return `_$b(${taccess}.$tsym, ${val})`;
    }

    private emitUnBoxOperation(val: string): string {
        return `(${val})._$val`;
    }

    private emitBUAsNeeded(val: string, oftype: TypeSignature, totype: TypeSignature): string {
        const oftypet = this.tproc(oftype);
        const totypet = this.tproc(totype);

        if(EmitNameManager.isNakedTypeRepr(oftypet) == EmitNameManager.isBoxedTypeRepr(totypet)) {
            return this.emitBoxOperation(val, totypet as NominalTypeSignature);
        }
        else if(EmitNameManager.isBoxedTypeRepr(oftypet) && EmitNameManager.isNakedTypeRepr(totypet)) {
            return this.emitUnBoxOperation(val);
        }
        else {
            return val;
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
        const errtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getErrType(), (vtype as NominalTypeSignature).alltermargs);

        return `${val}._$is(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), isnot ? errtype : oktype)}.$tsym)`;
    }

    private emitITestAsTest_Err(val: string, vtype: TypeSignature, isnot: boolean): string {
        const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
        const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
        const errtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getErrType(), (vtype as NominalTypeSignature).alltermargs);

        return `${val}._$is(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), isnot ? oktype : errtype)}.$tsym)`;
    }

    private emitITestAsTest_Type(val: string, oftype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isUniqueTypeForSubtypeChecking(oftype)) {
            return `${val}._$is${isnot ? "Not" : ""}(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), this.tproc(oftype) as NominalTypeSignature)}.$tsym)`;
        }
        else {
            return `${val}._$is${isnot ? "Not" : ""}Subtype(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), this.tproc(oftype) as NominalTypeSignature)}.$tsym)`;
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
                assert(tt instanceof ITestErr, "missing case in ITest");
                return this.emitITestAsTest_Err(val, vvtype, tt.isnot);
            }
        }
    }

    private emitITestAsConvert_None(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const emsg = this.getErrorInfo(isnot ? "expected None but got Some" : "expected Some but got None", sinfo, undefined);
            return val + (isnot ? `._$asNone(${emsg})` : `._$asSome(${emsg})`);
        }
    }

    private emitITestAsConvert_Some(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const emsg = this.getErrorInfo(isnot ? "expected Some but got None" : "expected None but got Some", sinfo, undefined);
            return val + (isnot ? `._$asSome(${emsg})` : `._$asNone(${emsg})`);
        }
    }

    private emitITestAsConvert_Ok(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
            const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
            const errtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getErrType(), (vtype as NominalTypeSignature).alltermargs);

            const emsg = this.getErrorInfo(isnot ? "expected Err but got Ok" : "expected Ok but got Err", sinfo, undefined);
            return `${val}._$as(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), isnot ? errtype : oktype)}.$tsym, true, ${emsg})`;
        }
    }

    private emitITestAsConvert_Err(sinfo: SourceInfo, val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
            const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
            const errtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getErrType(), (vtype as NominalTypeSignature).alltermargs);

            const emsg = this.getErrorInfo(isnot ? "expected Ok but got Err" : "expected Err but got Ok", sinfo, undefined);
            return `${val}._$as(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), isnot ? errtype : oktype)}.$tsym, true, ${emsg})`;
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
                return `${val}._$as${isnot ? "Not" : ""}(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), toftype)}.$tsym, ${ubx}, ${emsg})`;
            }
            else {
                const toftype = this.tproc(oftype) as NominalTypeSignature;
                const emsg = this.getErrorInfo(isnot ? `expected not subtype of ${toftype.tkeystr}` : `expected subtytype of ${toftype.tkeystr}`, sinfo, undefined);
                return `${val}._$as${isnot ? "Not" : ""}Subtype(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), toftype)}.$tsym, ${ubx}, ${emsg})`;
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
                assert(tt instanceof ITestErr, "missing case in ITest");
                return this.emitITestAsConvert_Err(sinfo, val, vvtype, tt.isnot);
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
        return `${exp.value.slice(0, -1)}n`;
    }

    private emitLiteralIntExpression(exp: LiteralSimpleExpression): string {
        return `${exp.value.slice(0, -1)}n`;
    }

    private emitLiteralBigNatExpression(exp: LiteralSimpleExpression): string {
        return `${exp.value.slice(0, -1)}n`;
    }

    private emitLiteralBigIntExpression(exp: LiteralSimpleExpression): string {
        return `${exp.value.slice(0, -1)}n`;
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
    
    private emitLiteralDateTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DateTime");
    }
    
    private emitLiteralUTCDateTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- UTCDateTime");
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
    
    private emitLiteralTickTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- TickTime");
    }
    
    private emitLiteralISOTimeStampExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- ISOTimeStamp");
    }
    
    private emitLiteralDeltaDateTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaDateTime");
    }
    
    private emitLiteralDeltaPlainDateExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaPlainDate");
    }
    
    private emitLiteralDeltaPlainTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaPlainTime");
    }
    
    private emitLiteralDeltaISOTimeStampExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaISOTimeStamp");
    }
    
    private emitLiteralDeltaSecondsExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaSeconds");
    }
    
    private emitLiteralDeltaTickExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- DeltaTick");
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
        return `validateStringLiteral(${exp.value})`;
    }
    
    private emitLiteralCStringExpression(exp: LiteralSimpleExpression): string {
        return `validateCStringLiteral(${exp.value})`;
    }
    
    private emitLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression, toplevel: boolean): string {
        assert(false, "Not implemented -- TypeDeclValue");
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
        const nsaccess = EmitNameManager.emitNamespaceAccess(this.getCurrentNamespace(), cns);

        return `${nsaccess}${exp.name}()`;
    }
    
    private emitAccessStaticFieldExpression(exp: AccessStaticFieldExpression): string {
        assert(false, "Not implemented -- AccessStaticField");
    }
    
    private emitAccessVariableExpression(exp: AccessVariableExpression): string {
        if(!exp.isCaptured) {
            if(exp.srcname === "this") {
                return "_$this";
            }
            else if(exp.srcname === "self") {
                return "_$self";
            }
            else {
                return exp.scopename;
            }
        }
        else {
            return exp.scopename;
        }
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

    private emitStandardConstructor(exp: ConstructorPrimaryExpression): string {
        const taccess = EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), this.tproc(exp.ctype) as NominalTypeSignature);

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
            return `${taccess}.$create(${exp.args.args.map((a) => this.emitExpression(a.exp, true)).join(", ")})`;
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

    private emitSpecialConstructorExpression(exp: SpecialConstructorExpression): string {
        assert(false, "Not implemented -- SpecialConstructor");
    }
    
    private emitCallNamespaceFunctionExpression(exp: CallNamespaceFunctionExpression): string {
        const cns = EmitNameManager.resolveNamespaceDecl(this.assembly, exp.ns);

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

        return `${EmitNameManager.emitNamespaceAccess(this.getCurrentNamespace(), cns)}.${exp.name}(${argl.join(", ")})`;
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
        if(EmitNameManager.isNakedTypeRepr(rcvrtype)) {
            return `${val}.${exp.name}`;
        }
        else {
            return `${val}._$val.${exp.name}`;
        }
    }

    private emitPostfixProjectFromNames(val: string, exp: PostfixProjectFromNames): string {
        assert(false, "Not Implemented -- checkPostfixProjectFromNames");
    }

    private emitPostfixAccessFromIndex(val: string, exp: PostfixAccessFromIndex): string {
        assert(false, "Not Implemented -- checkPostfixAccessFromIndex");
    }

    private emitPostfixIsTest(val: string, exp: PostfixIsTest): string {
        return this.processITestAsTest(val, this.tproc(exp.getRcvrType()), exp.ttest);
    }

    private emitPostfixAsConvert(val: string, exp: PostfixAsConvert): string {
        return this.processITestAsConvert(exp.sinfo, val, this.tproc(exp.getRcvrType()), exp.ttest);
    }

    private emitPostfixAssignFields(val: string, exp: PostfixAssignFields): string {
        assert(false, "Not Implemented -- checkPostfixAssignFields");
    }

    private emitPostfixInvoke(val: string, exp: PostfixInvoke): string {
        assert(false, "Not Implemented -- checkPostfixInvoke");
    }

    private emitPostfixLiteralKeyAccess(val: string, exp: PostfixLiteralKeyAccess): string {
        assert(false, "Not Implemented -- checkPostfixLiteralKeyAccess");
    }

    private emitPostfixOp(exp: PostfixOp, toplevel: boolean): string {
        let eexp = this.emitExpression(exp.rootExp, false);
    
        for(let i = 0; i < exp.ops.length; ++i) {
            const op = exp.ops[i];
            
            switch(op.tag) {
                case PostfixOpTag.PostfixAccessFromName: {
                    eexp = this.emitPostfixAccessFromName(eexp, op as PostfixAccessFromName);
                }
                case PostfixOpTag.PostfixProjectFromNames: {
                    eexp = this.emitPostfixProjectFromNames(eexp, op as PostfixProjectFromNames);
                }
                case PostfixOpTag.PostfixAccessFromIndex: {
                    eexp = this.emitPostfixAccessFromIndex(eexp, op as PostfixAccessFromIndex);
                }
                case PostfixOpTag.PostfixIsTest: {
                    eexp = this.emitPostfixIsTest(eexp, op as PostfixIsTest);
                }
                case PostfixOpTag.PostfixAsConvert: {
                    eexp = this.emitPostfixAsConvert(eexp, op as PostfixAsConvert);
                }
                case PostfixOpTag.PostfixAssignFields: {
                    eexp = this.emitPostfixAssignFields(eexp, op as PostfixAssignFields);
                }
                case PostfixOpTag.PostfixInvoke: {
                    eexp = this.emitPostfixInvoke(eexp, op as PostfixInvoke);
                }
                case PostfixOpTag.PostfixLiteralKeyAccess: {
                    eexp = this.emitPostfixLiteralKeyAccess(eexp, op as PostfixLiteralKeyAccess);
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
        return toplevel ? `(${eexp})` : eexp;
    }

    private emitPrefixNegateOrPlusOpExpression(exp: PrefixNegateOrPlusOpExpression, toplevel: boolean): string {
        const eexp = `${exp.op}${this.emitExpression(exp.exp, false)}`;
        return toplevel ? `(${eexp})` : eexp;
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
            return toplevel ? `(${eexp})` : eexp;
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
            return toplevel ? `(${eexp})` : eexp;
        }
        else if(kcop === "rhsnone") {
            const eexp = `${this.emitExpression(exp.lhs, false)} === null`;
            return toplevel ? `(${eexp})` : eexp;
        }
        else if(kcop === "lhskeyeqoption") {
            return `${this.emitExpression(exp.rhs, false)}._$keyEqOf(${this.emitExpression(exp.lhs, true)})`;
        }
        else if(kcop === "rhskeyeqoption") {
            return `${this.emitExpression(exp.lhs, false)}._$keyEqOf(${this.emitExpression(exp.rhs, true)})`;
        }
        else if(kcop === "stricteq") {
            const eexp = `${this.emitExpression(exp.lhs, false)} === ${this.emitExpression(exp.rhs, false)}`;
            return toplevel ? `(${eexp})` : eexp;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitBinKeyNeqExpression(exp: BinKeyNeqExpression, toplevel: boolean): string {
        const kcop = exp.operkind;

        if(kcop === "lhsnone") {
            const eexp = `${this.emitExpression(exp.rhs, false)} !== null`;
            return toplevel ? `(${eexp})` : eexp;
        }
        else if(kcop === "rhsnone") {
            const eexp = `${this.emitExpression(exp.lhs, false)} !== null`;
            return toplevel ? `(${eexp})` : eexp;
        }
        else if(kcop === "lhskeyeqoption") {
            return `${this.emitExpression(exp.rhs, false)}._$keyNeqOf(${this.emitExpression(exp.lhs, true)})`;
        }
        else if(kcop === "rhskeyeqoption") {
            return `${this.emitExpression(exp.lhs, false)}._$keyNeqOf(${this.emitExpression(exp.rhs, true)})`;
        }
        else if(kcop === "stricteq") {
            const eexp = `${this.emitExpression(exp.lhs, false)} !== ${this.emitExpression(exp.rhs, false)}`;
            return toplevel ? `(${eexp})` : eexp;
        }
        else {
            assert(false, "Unknown key eq kind");
        }
    }

    private emitNumericEqExpression(exp: NumericEqExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} === ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }

    private emitNumericNeqExpression(exp: NumericNeqExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} !== ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }
    
    private emitNumericLessExpression(exp: NumericLessExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} < ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }
    
    private emitNumericLessEqExpression(exp: NumericLessEqExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} <= ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }
    
    private emitNumericGreaterExpression(exp: NumericGreaterExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} > ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }

    private emitNumericGreaterEqExpression(exp: NumericGreaterEqExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} >= ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }

    private emitBinLogicAndExpression(exp: BinLogicAndExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} && ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }

    private emitBinLogicOrExpression(exp: BinLogicOrExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} || ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }

    private emitBinLogicImpliesExpression(exp: BinLogicImpliesExpression, toplevel: boolean): string {
        const eeexp = `!(${this.emitExpression(exp.lhs, false)} && !${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eeexp})` : eeexp;
    }

    private emitBinLogicIFFExpression(exp: BinLogicIFFExpression, toplevel: boolean): string {
        const eexp = `(${this.emitExpression(exp.lhs, false)} === ${this.emitExpression(exp.rhs, false)})`;
        return toplevel ? `(${eexp})` : eexp;
    }
    
    private emitMapEntryConstructorExpression(exp: MapEntryConstructorExpression): string {
        return `[${this.emitExpression(exp.kexp, true)}, ${this.emitExpression(exp.vexp, true)}]`;
    }

    private emitIfExpression(exp: IfExpression, toplevel: boolean): string {
        if(exp.test.itestopt === undefined) {
            const eexp = `${this.emitExpression(exp.test.exp, false)} ? ${this.emitExpression(exp.trueValue, false)} : ${this.emitExpression(exp.falseValue, false)}`;
            return toplevel ? `(${eexp})` : eexp;
        }
        else {
            const vval = this.emitExpression(exp.test.exp, true);
        
            if(exp.binder === undefined) {
                const ttest = this.processITestAsTest(vval, exp.test.exp.getType(), exp.test.itestopt);
                const eexp = `${ttest} ? ${this.emitExpression(exp.trueValue, false)} : ${this.emitExpression(exp.falseValue, false)}`;
                return toplevel ? `(${eexp})` : eexp;
            }
            else {
                this.bindernames.add(exp.binder.scopename);

                const ttest = this.processITestAsTest(exp.binder.scopename, exp.test.exp.getType(), exp.test.itestopt);
                const eexp = `(${exp.binder.scopename} = ${vval}, ${ttest}) ? ${this.emitExpression(exp.trueValue, false)} : ${this.emitExpression(exp.falseValue, false)}`;
                return toplevel ? `(${eexp})` : eexp;
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
            case ExpressionTag.LiteralDateTimeExpression: {
                return this.emitLiteralDateTimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUTCDateTimeExpression: {
                return this.emitLiteralUTCDateTimeExpression(exp as LiteralSimpleExpression);
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
            case ExpressionTag.LiteralTickTimeExpression: {
                return this.emitLiteralTickTimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralISOTimeStampExpression: {
                return this.emitLiteralISOTimeStampExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaDateTimeExpression: {
                return this.emitLiteralDeltaDateTimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaPlainDateExpression: {
                return this.emitLiteralDeltaPlainDateExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaPlainTimeExpression: {
                return this.emitLiteralDeltaPlainTimeExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaISOTimeStampExpression: {
                return this.emitLiteralDeltaISOTimeStampExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaSecondsExpression: {
                return this.emitLiteralDeltaSecondsExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaTickExpression: {
                return this.emitLiteralDeltaTickExpression(exp as LiteralSimpleExpression);
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
                return this.emitSpecialConstructorExpression(exp as SpecialConstructorExpression);
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
        const rhsexp = this.emitBUAsNeeded(this.emitExpressionRHS(stmt.exp), stmt.exp.getType(), stmt.actualtype || stmt.exp.getType());
        
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
        const check = this.processITestAsConvert(stmt.sinfo, stmt.name, this.tproc(stmt.vtype as TypeSignature), stmt.ttest);

        return `${stmt.name} = ${check};`;
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
                const bassign = `${stmt.binder.scopename} = ${this.emitExpression(stmt.cond.exp, true)};` + "\n" + fmt.indent("");
                const test = this.processITestAsTest(stmt.binder.scopename, stmt.cond.exp.getType(), stmt.cond.itestopt);
                const body = this.emitBlockStatement(stmt.trueBlock, fmt);

                if(!stmt.binder.refineonfollow) {
                    return `${bassign} if(${test}) ${body}`;
                }
                else {
                    return `${bassign} if(${test}) ${body} ${stmt.binder.refinefollowname} = ${this.emitBUAsNeeded(stmt.binder.scopename, this.tproc(stmt.binder.origtype as TypeSignature), this.tproc(stmt.binder.refinefollowtype as TypeSignature))};`;
                }
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
                const bassign = `${stmt.binder.scopename} = ${this.emitExpression(stmt.cond.exp, true)};` + "\n" + fmt.indent("");
                const test = this.processITestAsTest(stmt.binder.scopename, stmt.cond.exp.getType(), stmt.cond.itestopt);
                const tbody = this.emitBlockStatement(stmt.trueBlock, fmt);
                const fbody = this.emitBlockStatement(stmt.falseBlock, fmt);

                if(!stmt.binder.refineonfollow) {
                    return `${bassign} if(${test}) ${tbody}\n${fmt.indent("")}else ${fbody}`;
                }
                else {
                    return `${bassign} if(${test}) ${tbody}\n${fmt.indent("")}else ${fbody}${stmt.binder.refinefollowname} = ${this.emitBUAsNeeded(stmt.binder.scopename, this.tproc(stmt.binder.origtype as TypeSignature), this.tproc(stmt.binder.refinefollowtype as TypeSignature))};`;
                }
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
        return `$_abort(${this.getErrorInfo("abort", stmt.sinfo, undefined)});`;
    }

    private emitAssertStatement(stmt: AssertStatement): string {
        return `$_assert(${this.emitExpression(stmt.cond, true)}, ${this.getErrorInfo(stmt.cond.emit(true, new CodeFormatter()), stmt.sinfo, undefined)});`;
    }

    private emitValidateStatement(stmt: ValidateStatement): string {
        return `$_validate(${this.emitExpression(stmt.cond, true)}, ${this.getErrorInfo(stmt.cond.emit(true, new CodeFormatter()), stmt.sinfo, stmt.diagnosticTag)});`;
    }

    private emitDebugStatement(stmt: DebugStatement): string {
        return `try { console.log(${this.emitExpression(stmt.value, true)}); } catch { console.log("Error evaluating debug statement @ ${this.currentfile}:${stmt.sinfo.line}"); }`;
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
        let prevskip = false;
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

            if(this.bindernames.size === 0 && initializers.length === 0 && preconds.length === 0 && refsaves.length === 0) {
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
            assert(p.optDefaultValue !== undefined);

            inits.push(`if(${p.name} === undefined) { ${p.name} = ${this.emitExpression(p.optDefaultValue.exp, true)}; }`);
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

    private emitInvariants(bnames: {name: string, type: TypeSignature}[], invariants: InvariantDecl[]): string[] {
        const env = TypeEnvironment.createInitialStdEnv(bnames.map((bn) => new VarInfo("$" + bn.name, "$" + bn.name, bn.type, true, true)), this.getWellKnownType("Bool"), new SimpleTypeInferContext(this.getWellKnownType("Bool")));

        for(let i = 0; i < invariants.length; ++i) {
            const inv = invariants[i];
            const etype = this.checkExpression(env, inv.exp.exp, undefined);
            this.checkError(invariants[i].sinfo, !this.isBooleanType(etype), `Invariant expression does not have a boolean type -- got ${etype.tkeystr}`);
        }
    }

    private emitValidates(bnames: {name: string, type: TypeSignature}[], validates: ValidateDecl[]): string[] {
        const env = TypeEnvironment.createInitialStdEnv(bnames.map((bn) => new VarInfo("$" + bn.name, "$" + bn.name, bn.type, true, true)), this.getWellKnownType("Bool"), new SimpleTypeInferContext(this.getWellKnownType("Bool")));

        for(let i = 0; i < validates.length; ++i) {
            const etype = this.checkExpression(env, validates[i].exp.exp, undefined);
            this.checkError(validates[i].sinfo, !this.isBooleanType(etype), `Validate expression does not have a boolean type -- got ${etype.tkeystr}`);
        }
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

    private emitFunctionDecl(fdecl: FunctionInvokeDecl, optmapping: TemplateNameMapper | undefined, fmt: JSCodeFormatter): {body: string, resfimpl: string | undefined, tests: string[]} {
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

            resf = `${fdecl.name}$onreturn`;
            const resb = ensures.map((e) => fmt.indent(e)).join("\n");
            resfimpl = `function ${resf}(${fdecl.params.map((p) => p.name).join(", ")}, $return) {\n${resb}${fmt.indent("\n")}}`;
        }

        const body = this.emitBodyImplementation(fdecl.body, fdecl.resultType, initializers, preconds, refsaves, resf, fmt);
        this.mapper = undefined;

        return {body: `${sig} ${body}`, resfimpl: resfimpl, tests: tests};
    }

    private emitFunctionDecls(fdecls: [FunctionInvokeDecl, TemplateNameMapper[] | undefined][], fmt: JSCodeFormatter): {decls: string[], tests: string[]} {
        let decls: string[] = [];
        let tests: string[] = [];

        for(let i = 0; i < fdecls.length; ++i) {
            const fdecl = fdecls[i][0];
            const mappers = fdecls[i][1]; 
    
            if(mappers === undefined) {
                const {body, resfimpl, tests} = this.emitFunctionDecl(fdecl, undefined, fmt);
            
                if(resfimpl !== undefined) {
                    decls.push(resfimpl);
                }
                decls.push(body);

                tests.push(...tests);
            }
            else {
                for(let j = 0; j < mappers.length; ++j) {
                    const {body, resfimpl, tests} = this.emitFunctionDecl(fdecl, mappers[j], fmt);
            
                    if(resfimpl !== undefined) {
                        decls.push(resfimpl);
                    }
                    decls.push(body);

                    tests.push(...tests);
                }
            }
        }

        return {decls: decls, tests: tests};
    }

    private emitMethodDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecls: MethodDecl[]): {decls: string[], tests: string[]} {
        let decls: string[] = [];
        let tests: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {   
            assert(false, "Not implemented -- checkMethodDecl");
        }

        return {decls: decls, tests: tests};
    }

    private emitTaskMethodDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecls: TaskMethodDecl[]): string[] {
        let decls: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {
            assert(false, "Not implemented -- checkTaskMethodDecl");
        }

        return decls;
    }

    private emitTaskActionDecls(tdecl: AbstractNominalTypeDecl, rcvr: TypeSignature, mdecls: TaskActionDecl[]): string[] {
        let decls: string[] = [];

        for(let i = 0; i < mdecls.length; ++i) {
            assert(false, "Not implemented -- checkTaskActionDecl");
        }

        return decls;
    }

    private emitConstMemberDecls(tdecl: AbstractNominalTypeDecl, mdecls: ConstMemberDecl[]): string[] {
        let cdecls: string[] = [];
        for(let i = 0; i < mdecls.length; ++i) {
            const m = mdecls[i];

            const eexp = this.emitExpression(m.value.exp, true);
            const lexp = `() => ${eexp}`;

            cdecls.push(`${m.name}: () => _$memoconstval(this._$consts, "${m.name}", ${lexp};`);
        }

        return cdecls;
    }

    private emitAbstractNominalTypeDeclHelper(bnames: {name: string, type: TypeSignature}[], rcvr: TypeSignature, tdecl: AbstractNominalTypeDecl, mappings: TemplateNameMapper[] | undefined, optfdecls: MemberFieldDecl[] | undefined, isentity: boolean) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms);
        }

        this.checkProvides(tdecl.provides);

        //make sure all of the invariants on this typecheck
        this.checkInvariants(bnames, tdecl.invariants);
        this.checkValidates(bnames, tdecl.validates);
        
        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);
        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);

        if(optfdecls !== undefined) {
            this.checkMemberFieldDecls(bnames, optfdecls);
        }

        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, optfdecls, isentity);

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private emitEnumTypeDecl(ns: NamespaceDeclaration, tdecl: EnumTypeDecl): string {
        this.file = tdecl.file;
        this.checkError(tdecl.sinfo, tdecl.terms.length !== 0, "Enums cannot have template terms");
        
        this.checkProvides(tdecl.provides);
 
        //Make sure that any provides types are not adding on fields, consts, or functions
        const etype = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        const providesdecls = this.relations.resolveTransitiveProvidesDecls(etype, this.constraints);
        for(let i = 0; i < providesdecls.length; ++i) {
            const pdecl = providesdecls[i];
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).fields.length !== 0, `Provides type cannot have member fields -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).invariants.length !== 0 || (pdecl.tsig.decl as ConceptTypeDecl).validates.length !== 0, `Provides type cannot have invariants -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).consts.length !== 0, `Provides type cannot have consts -- ${pdecl.tsig.decl.name}`);
            this.checkError(tdecl.sinfo, (pdecl.tsig.decl as ConceptTypeDecl).functions.length !== 0, `Provides type cannot have functions -- ${pdecl.tsig.decl.name}`);
        }

        this.checkError(tdecl.sinfo, tdecl.invariants.length !== 0 || tdecl.validates.length !== 0, "Enums cannot have invariants");

        this.checkError(tdecl.sinfo, tdecl.consts.length !== 0, "Enums cannot have consts");
        this.checkError(tdecl.sinfo, tdecl.functions.length !== 0, "Enums cannot have functions");

        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []);
        this.checkMethodDecls(tdecl, rcvr, tdecl.methods);

        this.checkAbstractNominalTypeDeclVCallAndInheritance(tdecl, [], true);

        let opts = new Set<string>();
        for(let i = 0; i < tdecl.members.length; ++i) {
            this.checkError(tdecl.sinfo, opts.has(tdecl.members[i]), `Duplicate enum option ${tdecl.members[i]}`);
            opts.add(tdecl.members[i]);
        }
        this.file = CLEAR_FILENAME;
    }

    private emitTypedeclTypeDecl(ns: NamespaceDeclaration, tdecl: TypedeclTypeDecl, isentity: boolean): string {
        return "[TYPEDECL]";
    }

    private checkInteralSimpleTypeDeclHelper(ns: NamespaceDeclaration, tdecl: InternalEntityTypeDecl, isentity: boolean) {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        this.checkAbstractNominalTypeDeclHelper([], rcvr, tdecl, undefined, isentity);
    }

    private checkOkTypeDecl(ns: NamespaceDeclaration, tdecl: OkTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true)
    }

    private checkErrTypeDecl(ns: NamespaceDeclaration, tdecl: ErrTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkAPIRejectedTypeDecl(ns: NamespaceDeclaration, tdecl: APIRejectedTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkAPIFailedTypeDecl(ns: NamespaceDeclaration, tdecl: APIFailedTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkAPIErrorTypeDecl(ns: NamespaceDeclaration, tdecl: APIErrorTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkAPISuccessTypeDecl(ns: NamespaceDeclaration, tdecl: APISuccessTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkSomeTypeDecl(ns: NamespaceDeclaration, tdecl: SomeTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkMapEntryTypeDecl(ns: NamespaceDeclaration, tdecl: MapEntryTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkListTypeDecl(ns: NamespaceDeclaration, tdecl: ListTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkStackTypeDecl(ns: NamespaceDeclaration, tdecl: StackTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkQueueTypeDecl(ns: NamespaceDeclaration, tdecl: QueueTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkSetTypeDecl(ns: NamespaceDeclaration, tdecl: SetTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkMapTypeDecl(ns: NamespaceDeclaration, tdecl: MapTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkEventListTypeDecl(ns: NamespaceDeclaration, tdecl: EventListTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, true);
    }

    private checkEntityTypeDecl(ns: NamespaceDeclaration, tdecl: EntityTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, this.constraints, tdecl.fields);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);
        this.file = CLEAR_FILENAME;
    }

    private checkPrimitiveConceptTypeDecl(ns: NamespaceDeclaration, tdecl: PrimitiveConceptTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);
    }

    private checkOptionTypeDecl(ns: NamespaceDeclaration, tdecl: OptionTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);
    }

    private checkResultTypeDecl(ns: NamespaceDeclaration, tdecl: ResultTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);

        this.constraints.pushConstraintScope(tdecl.terms);
        for(let i = 0; i < tdecl.nestedEntityDecls.length; ++i) {
            const ned = tdecl.nestedEntityDecls[i];
            if(ned instanceof OkTypeDecl) {
                this.checkOkTypeDecl(ns, ned);
            }
            else {
                this.checkErrTypeDecl(ns, ned as ErrTypeDecl);
            }
        }
        this.constraints.popConstraintScope();
    }

    private checkAPIResultTypeDecl(ns: NamespaceDeclaration, tdecl: APIResultTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);

        this.constraints.pushConstraintScope(tdecl.terms);
        for(let i = 0; i < tdecl.nestedEntityDecls.length; ++i) {
            const ned = tdecl.nestedEntityDecls[i];
            if(ned instanceof APIRejectedTypeDecl) {
                this.checkAPIRejectedTypeDecl(ns, ned);
            }
            else if(ned instanceof APIFailedTypeDecl) {
                this.checkAPIFailedTypeDecl(ns, ned);
            }
            else if(ned instanceof APIErrorTypeDecl) {
                this.checkAPIErrorTypeDecl(ns, ned);
            }
            else {
                this.checkAPISuccessTypeDecl(ns, ned as APISuccessTypeDecl);
            }
        }
        this.constraints.popConstraintScope();
    }

    private checkExpandoableTypeDecl(ns: NamespaceDeclaration, tdecl: ExpandoableTypeDecl) {
        this.checkInteralSimpleTypeDeclHelper(ns, tdecl, false);
    }

    private checkConceptTypeDecl(ns: NamespaceDeclaration, tdecl: ConceptTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, this.constraints, tdecl.fields);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, false);
        this.file = CLEAR_FILENAME;
    }

    private checkDatatypeMemberEntityTypeDecl(ns: NamespaceDeclaration, parent: DatatypeTypeDecl, tdecl: DatatypeMemberEntityTypeDecl) {
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, this.constraints, tdecl.fields);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);
    }

    private checkDatatypeTypeDecl(ns: NamespaceDeclaration, tdecl: DatatypeTypeDecl) {
        this.file = tdecl.file;
        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = this.relations.generateAllFieldBNamesInfo(rcvr, this.constraints, tdecl.fields);

        this.checkAbstractNominalTypeDeclHelper(bnames, rcvr, tdecl, tdecl.fields, true);

        for(let i = 0; i < tdecl.associatedMemberEntityDecls.length; ++i) {
            this.checkDatatypeMemberEntityTypeDecl(ns, tdecl, tdecl.associatedMemberEntityDecls[i]);
        }
        this.file = CLEAR_FILENAME;
    }

    private checkEventInfo(einfo: TypeSignature) {
        const oksig = this.checkTypeSignature(einfo);
        if(oksig) {
            this.checkError(einfo.sinfo, !this.relations.isEventDataType(einfo), `Event type is not a valid event type -- ${einfo.tkeystr}`);
        }
    }

    private checkStatusInfo(sinfo: TypeSignature[]) {
        for(let i = 0; i < sinfo.length; ++i) {
            const oksig = this.checkTypeSignature(sinfo[i]);
            if(oksig) {
                this.checkError(sinfo[i].sinfo, !this.relations.isStatusDataType(sinfo[i]), `Event type is not a valid status type -- ${sinfo[i].tkeystr}`);
            }
        }
    }

    private checkEnvironmentVariableInformation(env: EnvironmentVariableInformation[]) {
        for(let i = 0; i < env.length; ++i) {
            assert(false, "Not implemented -- checkEnvironmentVariableInformation");
        }
    }

    private checkResourceInformation(res: ResourceInformation[] | "**" | "{}" | "?") {
        if(res === "**" || res === "{}" || res === "?") {
            return;
        }

        for(let i = 0; i < res.length; ++i) {
            assert(false, "Not implemented -- checkResourceInformation");
        }
    }

    private checkAPIDecl(adecl: APIDecl) {
        assert(false, "Not implemented -- checkAPIDecl");
    }

    private checkTaskDecl(ns: NamespaceDeclaration, tdecl: TaskDecl) {
        this.file = tdecl.file;
        this.checkTemplateTypesOnType(tdecl.sinfo, tdecl.terms);

        if(tdecl.terms.length !== 0) {
            this.constraints.pushConstraintScope(tdecl.terms);
        }

        const rcvr = new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, tdecl.terms.map((tt) => new TemplateTypeSignature(tdecl.sinfo, tt.name)));
        const bnames = tdecl.fields.map((f) => { return {name: f.name, type: f.declaredType}; });

        //make sure all of the invariants on this typecheck
        this.checkInvariants(bnames, tdecl.invariants);
        this.checkValidates(bnames, tdecl.validates);
        
        this.checkConstMemberDecls(tdecl, tdecl.consts);
        this.checkTypeFunctionDecls(tdecl, tdecl.functions);
        this.checkTaskMethodDecls(tdecl, rcvr, tdecl.selfmethods);
        this.checkTaskActionDecls(tdecl, rcvr, tdecl.actions);

        this.checkMemberFieldDecls(bnames, tdecl.fields);

        if(tdecl.implementsapi !== undefined) {
            assert(false, "Not implemented -- checkTaskDecl implementsapi");
        }
        else {
            if(tdecl.eventsInfo !== undefined) {
                this.checkEventInfo(tdecl.eventsInfo as TypeSignature);
            }
            if(tdecl.statusInfo !== undefined) {
                this.checkStatusInfo(tdecl.statusInfo as TypeSignature[]);
            }
            if(tdecl.envVarRequirementInfo !== undefined) {
                this.checkEnvironmentVariableInformation(tdecl.envVarRequirementInfo as EnvironmentVariableInformation[]);
            }
            if(tdecl.resourceImpactInfo !== undefined) {
                this.checkResourceInformation(tdecl.resourceImpactInfo as ResourceInformation[] | "**" | "{}" | "?");
            }
        }

        if(tdecl.terms.length !== 0) {
            this.constraints.popConstraintScope();
        }
        this.file = CLEAR_FILENAME;
    }

    private checkNamespaceConstDecls(cdecls: NamespaceConstDecl[]) {
        for(let i = 0; i < cdecls.length; ++i) {
            const m = cdecls[i];

            this.file = m.file;
            if(this.checkTypeSignature(m.declaredType)) {
                const infertype = this.relations.convertTypeSignatureToTypeInferCtx(m.declaredType, this.constraints);
                const decltype = this.checkExpression(TypeEnvironment.createInitialStdEnv([], m.declaredType, infertype), m.value.exp, m.declaredType);

                this.checkError(m.sinfo, !this.relations.isSubtypeOf(decltype, m.declaredType, this.constraints), `Const initializer does not match declared type -- expected ${m.declaredType.tkeystr} but got ${decltype.tkeystr}`);
            }
            this.file = CLEAR_FILENAME;
        }
    }

    private checkNamespaceTypeDecls(ns: NamespaceDeclaration, tdecl: AbstractNominalTypeDecl[]) {
        for(let i = 0; i < tdecl.length; ++i) {
            const tt = tdecl[i];

            if(tt instanceof EnumTypeDecl) {
                this.checkEnumTypeDecl(ns, tt);
            }
            else if(tt instanceof TypedeclTypeDecl) {
                this.checkTypedeclTypeDecl(ns, tt, true);
            }
            else if(tt instanceof PrimitiveEntityTypeDecl) {
                this.checkPrimitiveEntityTypeDecl(ns, tt);
            }
            else if(tt instanceof RegexValidatorTypeDecl) {
                this.checkRegexValidatorTypeDecl(ns, tt);
            }
            else if(tt instanceof CRegexValidatorTypeDecl) {
                this.checkCRegexValidatorTypeDecl(ns, tt);
            }
            else if(tt instanceof PathValidatorTypeDecl) {
                this.checkPathValidatorTypeDecl(ns, tt);
            }
            else if(tt instanceof StringOfTypeDecl) {
                this.checkStringOfTypeDecl(ns, tt);
            }
            else if(tt instanceof CStringOfTypeDecl) {
                this.checkCStringOfTypeDecl(ns, tt);
            }
            else if(tt instanceof PathOfTypeDecl) {
                this.checkPathOfTypeDecl(ns, tt);
            }
            else if(tt instanceof PathFragmentOfTypeDecl) {
                this.checkPathFragmentOfTypeDecl(ns, tt);
            }
            else if(tt instanceof PathGlobOfTypeDecl) {
                this.checkPathGlobOfTypeDecl(ns, tt);
            }
            else if(tt instanceof OkTypeDecl) {
                this.checkOkTypeDecl(ns, tt);
            }
            else if(tt instanceof ErrTypeDecl) {
                this.checkErrTypeDecl(ns, tt);
            }
            else if(tt instanceof APIRejectedTypeDecl) {
                this.checkAPIRejectedTypeDecl(ns, tt);
            }
            else if(tt instanceof APIFailedTypeDecl) {
                this.checkAPIFailedTypeDecl(ns, tt);
            }
            else if(tt instanceof APIErrorTypeDecl) {
                this.checkAPIErrorTypeDecl(ns, tt);
            }
            else if(tt instanceof APISuccessTypeDecl) {
                this.checkAPISuccessTypeDecl(ns, tt);
            }
            else if(tt instanceof SomeTypeDecl) {
                this.checkSomeTypeDecl(ns, tt);
            }
            else if(tt instanceof MapEntryTypeDecl) {
                this.checkMapEntryTypeDecl(ns, tt);
            }
            else if(tt instanceof ListTypeDecl) {
                this.checkListTypeDecl(ns, tt);
            }
            else if(tt instanceof StackTypeDecl) {
                this.checkStackTypeDecl(ns, tt);
            }
            else if(tt instanceof QueueTypeDecl) {
                this.checkQueueTypeDecl(ns, tt);
            }
            else if(tt instanceof SetTypeDecl) {
                this.checkSetTypeDecl(ns, tt);
            }
            else if(tt instanceof MapTypeDecl) {
                this.checkMapTypeDecl(ns, tt);
            }
            else if(tt instanceof EventListTypeDecl) {
                this.checkEventListTypeDecl(ns, tt);
            }
            else if(tt instanceof EntityTypeDecl) {
                this.checkEntityTypeDecl(ns, tt);
            }
            else if(tt instanceof PrimitiveConceptTypeDecl) {
                this.checkPrimitiveConceptTypeDecl(ns, tt);
            }
            else if(tt instanceof OptionTypeDecl) {
                this.checkOptionTypeDecl(ns, tt);
            }
            else if(tt instanceof ResultTypeDecl) {
                this.checkResultTypeDecl(ns, tt);
            }
            else if(tt instanceof APIResultTypeDecl) {
                this.checkAPIResultTypeDecl(ns, tt);
            }
            else if(tt instanceof ExpandoableTypeDecl) {
                this.checkExpandoableTypeDecl(ns, tt);
            }
            else if(tt instanceof ConceptTypeDecl) {
                this.checkConceptTypeDecl(ns, tt);
            }
            else if(tt instanceof DatatypeTypeDecl) {
                this.checkDatatypeTypeDecl(ns, tt);
            }
            else {
                assert(false, "Unknown type decl kind");
            }
        }
    }

    private emitNamespaceDeclaration(decl: NamespaceDeclaration): string {
        //all usings should be resolved and valid so nothing to do there

        this.checkNamespaceConstDecls(decl.consts);
        this.checkNamespaceFunctionDecls(decl.functions);
        this.checkNamespaceTypeDecls(decl, decl.typedecls);

        for(let i = 0; i < decl.apis.length; ++i) {
            this.checkAPIDecl(decl.apis[i]);
        }

        for(let i = 0; i < decl.tasks.length; ++i) {
            this.checkTaskDecl(decl, decl.tasks[i]);
        }

        for(let i = 0; i < decl.subns.length; ++i) {
            this.checkNamespaceDeclaration(decl.subns[i]);
        }
    }

    static emitAssembly(assembly: Assembly, mode: "release" | "testing" | "debug"): {ns: FullyQualifiedNamespace, contents: string}[] {
        const emitter = new JSEmitter(assembly, mode == "release" ? "release" : "debug", mode === "testing");

        //emit each of the assemblies
        let results: {ns: FullyQualifiedNamespace, contents: string}[] = [];
        for(let i = 0; i < assembly.toplevelNamespaces.length; ++i) {
            const nsdecl = assembly.toplevelNamespaces[i];
            const code = emitter.emitNamespaceDeclaration(nsdecl);

            results.push({ns: nsdecl.fullnamespace, contents: code});
        }

        return results;
    }
}

export {
    JSEmitter
};
