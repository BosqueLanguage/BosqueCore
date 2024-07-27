import assert from "node:assert";

import { JSCodeFormatter, EmitNameManager } from "./jsemitter_support.js";
import { AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, Expression, ExpressionTag, IfExpression, InterpolateExpression, ITest, ITestErr, ITestNone, ITestOk, ITestSome, ITestType, LambdaInvokeExpression, LetExpression, LiteralPathExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTemplateStringExpression, LiteralTypeDeclFloatPointValueExpression, LiteralTypeDeclIntegralValueExpression, LiteralTypeDeclValueExpression, LiteralTypedStringExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PostfixProjectFromNames, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, SpecialConstructorExpression, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskMultiExpression, TaskRaceExpression, TaskRunExpression } from "../frontend/body.js";
import { AbstractCollectionTypeDecl, Assembly, ConstructableTypeDecl, ListTypeDecl, MapEntryTypeDecl, NamespaceDeclaration, NamespaceFunctionDecl, PairTypeDecl, ResultTypeDecl } from "../frontend/assembly.js";
import { NominalTypeSignature, TemplateNameMapper, TypeSignature } from "../frontend/type.js";

class JSEmitter {
    readonly assembly: Assembly;
    readonly fmt: JSCodeFormatter;

    currentfile: string | undefined;
    currentns: NamespaceDeclaration | undefined;

    mapper: TemplateNameMapper | undefined;

    constructor(assembly: Assembly) {
        this.assembly = assembly;
        this.fmt = new JSCodeFormatter(0);
        
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

    private getCurrentFile(): string {
        assert(this.currentfile !== undefined, "Current file is not set");
        return this.currentfile;
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
        return `${val}._$is${isnot ? "Not" : ""}(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), this.tproc(oftype) as NominalTypeSignature)}.$tsym)`;
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

    private emitITestAsConvert_None(val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            return val + (isnot ? `._$asNone()` : `._$asSome()`);
        }
    }

    private emitITestAsConvert_Some(val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            return val + (isnot ? `._$asSome()` : `._$asNone()`);
        }
    }

    private emitITestAsConvert_Ok(val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
            const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
            const errtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getErrType(), (vtype as NominalTypeSignature).alltermargs);

            return `${val}._$as(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), isnot ? errtype : oktype)}.$tsym, true)`;
        }
    }

    private emitITestAsConvert_Err(val: string, vtype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return val;
        }
        else {
            const rdcel = this.assembly.getCoreNamespace().typedecls.find((td) => td.name === "Result") as ResultTypeDecl;
            const oktype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getOkType(), (vtype as NominalTypeSignature).alltermargs);
            const errtype = new NominalTypeSignature(vtype.sinfo, undefined, rdcel.getErrType(), (vtype as NominalTypeSignature).alltermargs);

            return `${val}._$as(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), isnot ? errtype : oktype)}.$tsym, true)`;
        }
    }

    private emitITestAsConvert_Type(val: string, vtype: TypeSignature, oftype: TypeSignature, isnot: boolean): string {
        if(EmitNameManager.isNakedTypeRepr(vtype)) {
            return EmitNameManager.isBoxedTypeRepr(oftype) ? `_$b${val}` : val;
        }
        else {
            const ubx = EmitNameManager.isNakedTypeRepr(oftype);
            return `${val}._$as${isnot ? "Not" : ""}(${EmitNameManager.emitTypeAccess(this.getCurrentNamespace(), this.tproc(oftype) as NominalTypeSignature)}.$tsym, ${ubx})`;
        }
    }
    
    private processITestAsConvert(val: string, vtype: TypeSignature, tt: ITest): string {
        const vvtype = this.tproc(vtype);
        
        if(tt instanceof ITestType) {
            return this.emitITestAsConvert_Type(val, vvtype, this.tproc(tt.ttype), tt.isnot);
        }
        else {
            if(tt instanceof ITestNone) {
                return this.emitITestAsConvert_None(val, vvtype, tt.isnot);
            }
            else if(tt instanceof ITestSome) {
                return this.emitITestAsConvert_Some(val, vvtype, tt.isnot);
            }
            else if(tt instanceof ITestOk) {
                return this.emitITestAsConvert_Ok(val, vvtype, tt.isnot);
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                return this.emitITestAsConvert_Err(val, vvtype, tt.isnot);
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
    
    private emitLiteralTypedStringExpression(exp: LiteralTypedStringExpression): string {
        assert(false, "Not implemented -- TypedString");
    }
    
    private emitLiteralTypedCStringExpression(exp: LiteralTypedStringExpression): string {
        assert(false, "Not implemented -- TypedCString");
    }
    
    private emitLiteralTemplateStringExpression(exp: LiteralTemplateStringExpression): string {
        assert(false, "Not implemented -- TemplateString");
    }
    
    private emitLiteralTemplateCStringExpression(exp: LiteralTemplateStringExpression): string {
        assert(false, "Not implemented -- TemplateCString");
    }
    
    private emitLiteralPathExpression(exp: LiteralPathExpression): string {
        assert(false, "Not implemented -- Path");
    }
    
    private emitLiteralPathFragmentExpression(exp: LiteralPathExpression): string {
        assert(false, "Not implemented -- PathFragment");
    }
    
    private emitLiteralPathGlobExpression(exp: LiteralPathExpression): string {
        assert(false, "Not implemented -- PathGlob");
    }
    
    private emitLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression, toplevel: boolean): string {
        assert(false, "Not implemented -- TypeDeclValue");
    }
    
    private emitLiteralTypeDeclIntegralValueExpression(exp: LiteralTypeDeclIntegralValueExpression, toplevel: boolean): string {
        assert(false, "Not implemented -- TypeDeclIntegralValue");
    }
    
    private emitLiteralTypeDeclFloatPointValueExpression(exp: LiteralTypeDeclFloatPointValueExpression, toplevel: boolean): string {
        assert(false, "Not implemented -- TypeDeclFloatPointValue");
    }

    private emitInterpolateExpression(exp: InterpolateExpression): string {
        assert(false, "Not implemented -- Interpolate");
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

        return `${nsaccess}${exp.name}`;
    }
    
    private emitAccessStaticFieldExpression(exp: AccessStaticFieldExpression): string {
        assert(false, "Not implemented -- AccessStaticField");
    }
    
    private emitAccessVariableExpression(exp: AccessVariableExpression): string {
        if(!exp.isCaptured) {
            return exp.scopename;
        }
        else {
            return exp.scopename;
        }
    }
    
    private emitCollectionConstructor(cdecl: AbstractCollectionTypeDecl, exp: ConstructorPrimaryExpression): string {
        if(cdecl instanceof ListTypeDecl) {
            return `[${exp.args.args.map((a) => this.emitBUAsNeeded(this.emitExpression(a.exp, true), a.exp.getType(), exp.elemtype as TypeSignature)).join(", ")}]`;
        }
        else {
            assert(false, "Unknown collection type -- emitCollectionConstructor");
        }
    }

    private emitSpecialConstructableConstructor(cdecl: ConstructableTypeDecl, exp: ConstructorPrimaryExpression, toplevel: boolean): string {
        if(cdecl instanceof PairTypeDecl || cdecl instanceof MapEntryTypeDecl) {
            const pairtype = exp.ctype as NominalTypeSignature;
            const pairargs = exp.args.args;
            const p0exp = this.emitBUAsNeeded(this.emitExpression(pairargs[0].exp, true),  pairargs[0].exp.getType(), pairtype.alltermargs[0]);
            const p1exp = this.emitBUAsNeeded(this.emitExpression(pairargs[1].exp, true),  pairargs[1].exp.getType(), pairtype.alltermargs[1]);
            return `[${p0exp}, ${p1exp}]`;
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
                argl.push(`[${restl.join(", ")}]`);
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

    private emitPostfixIsTest(val: string, exp: PostfixIsTest): string {
        return this.processITestAsTest(val, this.tproc(exp.getRcvrType()), exp.ttest);
    }

    private emitPostfixAsConvert(val: string, exp: PostfixAsConvert): string {
        return this.processITestAsConvert(val, this.tproc(exp.getRcvrType()), exp.ttest);
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

    private emitBinAddExpression(exp: BinAddExpression, toplevel: boolean): string {
        xxxx;
    }

    private emitBinSubExpression(exp: BinSubExpression, toplevel: boolean): string {
        xxxx;
    }
    
    private emitBinMultExpression(exp: BinMultExpression, toplevel: boolean): string {
        xxxx;
    }
    
    private emitBinDivExpression(exp: BinDivExpression, toplevel: boolean): string {
        xxxx;
    }
    
    private emitBinKeyEqExpression(exp: BinKeyEqExpression, toplevel: boolean): string {
        xxxx;
    }

    private emitBinKeyNeqExpression(exp: BinKeyNeqExpression, toplevel: boolean): string {
        xxxx;
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
        xxxx;
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
            case ExpressionTag.LiteralTypedStringExpression: {
                return this.emitLiteralTypedStringExpression(exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralTypedCStringExpression: {
                return this.emitLiteralTypedCStringExpression(exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralTemplateStringExpression: {
                return this.emitLiteralTemplateStringExpression(exp as LiteralTemplateStringExpression);
            }
            case ExpressionTag.LiteralTemplateCStringExpression: {
                return this.emitLiteralTemplateCStringExpression(exp as LiteralTemplateStringExpression);
            }
            case ExpressionTag.LiteralPathExpression: {
                return this.emitLiteralPathExpression(exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralPathFragmentExpression: {
                return this.emitLiteralPathFragmentExpression(exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralPathGlobExpression: {
                return this.emitLiteralPathGlobExpression(exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralTypeDeclValueExpression: {
                return this.emitLiteralTypeDeclValueExpression(exp as LiteralTypeDeclValueExpression, toplevel);
            }
            case ExpressionTag.LiteralTypeDeclIntegralValueExpression: {
                return this.emitLiteralTypeDeclIntegralValueExpression(exp as LiteralTypeDeclIntegralValueExpression, toplevel);
            }
            case ExpressionTag.LiteralTypeDeclFloatPointValueExpression: {
                return this.emitLiteralTypeDeclFloatPointValueExpression(exp as LiteralTypeDeclFloatPointValueExpression, toplevel);
            }
            case ExpressionTag.InterpolateExpression: {
                return this.emitInterpolateExpression(exp as InterpolateExpression);
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

    private checkExpressionRHS(exp: Expression): string {
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
}

export {
    JSEmitter
};
