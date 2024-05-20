import {strict as assert} from "assert";

import { Assembly } from "./assembly";
import { BuildLevel, SourceInfo } from "./build_decls";
import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, NominalTypeSignature, StringTemplateType, TemplateConstraintScope, TypeSignature, VoidTypeSignature } from "./type";
import { AbortStatement, AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BlockStatement, CallNamespaceFunctionExpression, CallRefSelfExpression, CallRefThisExpression, CallTaskActionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, ConstructorRecordExpression, ConstructorTupleExpression, DebugStatement, EmptyStatement, EnvironmentBracketStatement, EnvironmentUpdateStatement, Expression, ExpressionTag, ITest, ITestErr, ITestLiteral, ITestNone, ITestNothing, ITestOk, ITestSome, ITestSomething, ITestType, IfExpression, IfStatement, InterpolateExpression, LambdaInvokeExpression, LetExpression, LiteralExpressionValue, LiteralPathExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralSingletonExpression, LiteralTemplateStringExpression, LiteralTypeDeclFloatPointValueExpression, LiteralTypeDeclIntegralValueExpression, LiteralTypeDeclValueExpression, LiteralTypedStringExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PostfixProjectFromIndecies, PostfixProjectFromNames, PrefixNegateOpExpression, PrefixNotOpExpression, ReturnStatement, SelfUpdateStatement, SpecialConstructorExpression, StandaloneExpressionStatement, Statement, StatementTag, StringSliceExpression, SwitchStatement, TaskAccessInfoExpression, TaskAllExpression, TaskDashExpression, TaskEventEmitStatement, TaskMultiExpression, TaskRaceExpression, TaskRunExpression, TaskStatusStatement, TaskYieldStatement, ThisUpdateStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement } from "./body";
import { TypeEnvironment, VarInfo } from "./checker_environment";
import { AndRegexValidatorPack, OrRegexValidatorPack, RegexValidatorPack, SingleRegexValidatorPack, TypeCheckerResolver } from "./checker_resolver";
import { TypeCheckerRelations } from "./checker_relations";

const { accepts } = require("@bosque/jsbrex");

const MIN_SAFE_INT = -9223372036854775807n;
const MAX_SAFE_INT = 9223372036854775807n;

//negation and conversion are always safe
const MAX_SAFE_NAT = 9223372036854775807n;

class TypeError {
    readonly file: string;
    readonly line: number;
    readonly msg: string;

    constructor(file: string, line: number, msg: string) {
        this.file = file;
        this.line = line;
        this.msg = `Type error on ${line} -- ${msg}`;
    }
}

class TypeChecker {
    private readonly assembly: Assembly;
    private readonly buildLevel: BuildLevel;

    private readonly file: string;
    private readonly ns: FullyQualifiedNamespace;

    private readonly wellknownTypes: Map<string, TypeSignature>;

    private rtype: TypeSignature;

    readonly errors: TypeError[] = [];

    readonly constraints: TemplateConstraintScope;
    readonly resolver: TypeCheckerResolver;
    readonly relations: TypeCheckerRelations;

    constructor(assembly: Assembly, buildlevel: BuildLevel, file: string, ns: FullyQualifiedNamespace, wellknownTypes: Map<string, TypeSignature>) {
        this.assembly = assembly;
        this.buildLevel = buildlevel;

        this.file = file;
        this.ns = ns;

        this.wellknownTypes = wellknownTypes;

        this.rtype = new VoidTypeSignature(SourceInfo.implicitSourceInfo());
    }

    private reportError(sinfo: SourceInfo, msg: string) {
        this.errors.push(new TypeError(this.file, sinfo.line, msg));
    }

    private checkError(sinfo: SourceInfo, cond: boolean, msg: string): boolean {
        if (cond) {
            this.reportError(sinfo, msg);
        }

        return cond;
    }

    getErrorList(): TypeError[] {
        return this.errors;
    }

    private getWellKnownType(name: string): TypeSignature {
        assert(this.wellknownTypes.has(name), `Well known type ${name} not found`);
        return this.wellknownTypes.get(name) as TypeSignature;
    }

    private processITest_None(src: TypeSignature, isnot: boolean): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        const rinfo = this.relations.refineType(src, this.getWellKnownType("None"));
        return { ttrue: isnot ? rinfo.remain : rinfo.overlap, tfalse: isnot ? rinfo.overlap : rinfo.remain };
    }

    private processITest_Some(src: TypeSignature, isnot: boolean): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        const rinfo = this.relations.refineType(src, this.getWellKnownType("Some"));
        return { ttrue: isnot ? rinfo.remain : rinfo.overlap, tfalse: isnot ? rinfo.overlap : rinfo.remain };
    }

    private processITest_Nothing(src: TypeSignature, isnot: boolean): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        const rinfo = this.relations.refineType(src, this.getWellKnownType("Nothing"));
        return { ttrue: isnot ? rinfo.remain : rinfo.overlap, tfalse: isnot ? rinfo.overlap : rinfo.remain };
    }

    private processITest_Something(src: TypeSignature, isnot: boolean): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        const rinfo = this.relations.refineType(src, this.getWellKnownType("ISomething"));
        return { ttrue: isnot ? rinfo.remain : rinfo.overlap, tfalse: isnot ? rinfo.overlap : rinfo.remain };
    }

    private processITest_Ok(src: TypeSignature, isnot: boolean): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        const rinfo = this.relations.refineType(src, this.getWellKnownType("IOk"));
        return { ttrue: isnot ? rinfo.remain : rinfo.overlap, tfalse: isnot ? rinfo.overlap : rinfo.remain };
    }

    private processITest_Err(src: TypeSignature, isnot: boolean): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        const rinfo = this.relations.refineType(src, this.getWellKnownType("IErr"));
        return { ttrue: isnot ? rinfo.remain : rinfo.overlap, tfalse: isnot ? rinfo.overlap : rinfo.remain };
    }

    private processITest_Literal(env: TypeEnvironment, src: TypeSignature, literaltype: TypeSignature, isnot: boolean): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        const rinfo = this.relations.refineType(src, literaltype);
        return { ttrue: isnot ? rinfo.remain : rinfo.overlap, tfalse: isnot ? rinfo.overlap : rinfo.remain };
    }

    private processITest_Type(src: TypeSignature, oftype: TypeSignature, isnot: boolean): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        const rinfo = this.relations.refineType(src, oftype);
        return { ttrue: isnot ? rinfo.remain : rinfo.overlap, tfalse: isnot ? rinfo.overlap : rinfo.remain };
    }
    
    private processITest(sinfo: SourceInfo, env: TypeEnvironment, src: TypeSignature, tt: ITest): { ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined } {
        if(tt instanceof ITestType) {
            this.checkTypeSignature(env, tt.ttype);
            return this.processITest_Type(src, tt.ttype, tt.isnot);
        }
        else if(tt instanceof ITestLiteral) {
            const ll = this.resolver.compileTimeReduceConstantExpression(tt.literal.exp);
            if(ll === undefined) {
                this.reportError(sinfo, "Invalid literal expression value");
                return { ttrue: src, tfalse: src };
            }
            else {
                let lltype: TypeSignature;
                if(ll[1] !== undefined) {
                    lltype = ll[1].remapTemplateBindings(ll[2]);
                }
                else {
                    lltype = this.checkExpression(env, ll[0], undefined);
                }
                this.checkTypeSignature(env, lltype);
                this.checkError(sinfo, !(lltype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(lltype, this.getWellKnownType("KeyType"), env.binds), "Literal value must be a key type");

                return this.processITest_Literal(env, src, lltype, tt.isnot);
            }
        }
        else {
            if(tt instanceof ITestNone) {
                return this.processITest_None(src, tt.isnot);
            }
            else if(tt instanceof ITestSome) {
                return this.processITest_Some(src, tt.isnot);
            }
            else if(tt instanceof ITestNothing) {
                return this.processITest_Nothing(src, tt.isnot);
            }
            else if(tt instanceof ITestSomething) {
                return this.processITest_Something(src, tt.isnot);
            }
            else if(tt instanceof ITestOk) {
                return this.processITest_Ok(src, tt.isnot);
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                return this.processITest_Err(src, tt.isnot);
            }
        }
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

    //Given a type signature -- check that is is well formed and report any issues
    private checkTypeSignature(env: TypeEnvironment, type: TypeSignature): boolean {
        xxxx;
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

    private isLambdaTypedExpression(e: Expression, env: ExpressionTypeEnvironment): boolean {
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

    private checkValueEq(lhsexp: Expression, lhs: TypeSignature, rhsexp: Expression, rhs: TypeSignature): "err" | "truealways" | "falsealways" | "lhsnone" | "rhsnone" | "lhsnothing" | "rhsnothing" | "lhssomekey" | "rhssomekey" | "lhssomekeywithunique" | "rhssomekeywithunique" | "stdkey" | "stdkeywithunique" {
        if (lhsexp.tag === ExpressionTag.LiteralNoneExpression && rhsexp.tag === ExpressionTag.LiteralNoneExpression) {
            return "truealways";
        }

        if (lhsexp.tag === ExpressionTag.LiteralNothingExpression && rhsexp.tag === ExpressionTag.LiteralNothingExpression) {
            return "truealways";
        }

        if (lhsexp.tag === ExpressionTag.LiteralNoneExpression) {
            return this.relations.includesNoneType(rhs, this.constraints) ? "lhsnone" : "falsealways";
        }

        if (rhsexp.tag === ExpressionTag.LiteralNoneExpression) {
            return this.relations.includesNoneType(lhs, this.constraints) ? "rhsnone" : "falsealways";
        }

        if (lhsexp.tag === ExpressionTag.LiteralNothingExpression) {
            return this.relations.includesNothingType(rhs, this.constraints) ? "lhsnothing" : "falsealways";
        }

        if (rhsexp.tag === ExpressionTag.LiteralNothingExpression) {
            return this.relations.includesNothingType(lhs, this.constraints) ? "rhsnothing" : "falsealways";
        }

        //should be a subtype on one of the sides
        if (!this.relations.isSubtypeOf(lhs, rhs, this.constraints) && !this.relations.isSubtypeOf(rhs, lhs, this.constraints)) {
            return "err";
        }

        if (this.relations.areSameTypes(lhs, rhs, this.constraints)) {
            if(this.relations.isUniqueType(lhs, this.constraints) && this.relations.isUniqueType(rhs, this.constraints)) { 
                return "stdkeywithunique";
            }
            else {
                return "stdkey"
            }
        }
        else {
            if(this.relations.isSubtypeOf(lhs, rhs, this.constraints)) {
                if(this.relations.isUniqueType(lhs, this.constraints)) {
                    return "lhssomekeywithunique";
                }
                else {
                    return "lhssomekey";
                }
            }
            else {
                if(this.relations.isUniqueType(rhs, this.constraints)) {
                    return "rhssomekeywithunique";
                }
                else {
                    return "rhssomekey";
                }
            }
        }
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

    private checkLiteralNoneExpression(env: TypeEnvironment, exp: LiteralSingletonExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("None"));
    }

    private checkLiteralNothingExpression(env: TypeEnvironment, exp: LiteralSingletonExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("Nothing"));
    }

    private checkLiteralBoolExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkLiteralNatExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = BigInt(exp.value.slice(0, exp.value.length - 1));
        this.checkError(exp.sinfo, nval < 0n, "Nat literal cannot be negative");
        this.checkError(exp.sinfo, MAX_SAFE_NAT < nval, "Nat literal out of valid range");

        return exp.setType(this.getWellKnownType("Nat"));
    }

    private checkLiteralIntExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = BigInt(exp.value.slice(0, exp.value.length - 1));
        this.checkError(exp.sinfo, nval < MIN_SAFE_INT, "Int literal cannot be negative");
        this.checkError(exp.sinfo, MAX_SAFE_INT < nval, "Int literal out of valid range");

        return exp.setType(this.getWellKnownType("Nat"));
    }

    private checkLiteralBigNatExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const nval = BigInt(exp.value.slice(0, exp.value.length - 1));
        this.checkError(exp.sinfo, nval < 0n, "BigNat literal cannot be negative");

        return exp.setType(this.getWellKnownType("BigNat"));
    }

    private checkLiteralBigIntExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("BigInt"));
    }

    private checkLiteralRationalExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const slpos = exp.value.indexOf("/");
        const den = BigInt(exp.value.slice(slpos + 1, -1));

        this.checkError(exp.sinfo, MAX_SAFE_NAT < den, "Rational literal denominator out of valid range");

        return exp.setType(this.getWellKnownType("Rational"));
    }

    private static isValidFloatLiteral(val: string): boolean {
        const fval = Number.parseFloat(val);
        return !Number.isNaN(fval) && Number.isFinite(fval);
    }

    private static isValidDecimalLiteral(val: string): boolean {
        //TODO: we need to do a bit more on the bounds etc. here
        return true;
    }

    private static isValidDecimalDegreeLiteral(val: string): boolean {
        //TODO we need to do a bit more on the bounds and precision here -- e.g. 8 decimal places or more???
        return true;
    }

    private checkLiteralFloatExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        this.checkError(exp.sinfo, TypeChecker.isValidFloatLiteral(exp.value.slice(0, exp.value.length - 1)), "Invalid Float literal");

        return exp.setType(this.getWellKnownType("Float"));
    }

    private checkLiteralDecimalExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        this.checkError(exp.sinfo, TypeChecker.isValidDecimalLiteral(exp.value.slice(0, exp.value.length - 1)), "Invalid Decimal literal");

        return exp.setType(this.getWellKnownType("Decimal"));
    }

    private checkLiteralDecimalDegreeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        this.checkError(exp.sinfo, TypeChecker.isValidDecimalDegreeLiteral(exp.value.slice(0, exp.value.length - 2)), "Invalid DecimalDegree literal");

        return exp.setType(this.getWellKnownType("DecimalDegree"));
    }

    private checkLiteralLatLongCoordinateExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        const latsplit = exp.value.indexOf("lat");
        const latval = exp.value.slice(0, latsplit);
        const longval = exp.value.slice(latsplit + 3, exp.value.length - 4);

        this.checkError(exp.sinfo, TypeChecker.isValidDecimalDegreeLiteral(latval) && TypeChecker.isValidDecimalDegreeLiteral(longval), "Invalid Latitude value");

        return exp.setType(this.getWellKnownType("LatLongCoordinate"));
    }

    private checkLiteralComplexNumberExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        let spos = exp.value.lastIndexOf("+");
        if(spos === -1) {
            spos = exp.value.lastIndexOf("-");
        }

        const realval = exp.value.slice(0, spos);
        const imagval = exp.value.slice(spos, exp.value.length - 1);

        this.checkError(exp.sinfo, TypeChecker.isValidFloatLiteral(realval) && TypeChecker.isValidFloatLiteral(imagval), "Invalid Complex literal");

        return exp.setType(this.getWellKnownType("Complex"));
    }

    private checkLiteralByteBufferExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("ByteBuffer"));
    }

    private checkLiteralUUIDv4Expression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("UUIDv4"));
    }

    private checkLiteralUUIDv7Expression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("UUIDv7"));
    }

    private checkLiteralSHAContentHashExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("SHAContentHash"));
    }

    private checkLiteralDateTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here
        return exp.setType(this.getWellKnownType("DateTime"));
    }

    private checkLiteralUTCDateTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here -- also leap seconds
        return exp.setType(this.getWellKnownType("UTCDateTime"));
    }

    private checkLiteralPlainDateExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here
        return exp.setType(this.getWellKnownType("PlainDate"));
    }

    private checkLiteralPlainTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("PlainTime"));
    }

    private checkLiteralLogicalTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("LogicalTime"));
    }

    private checkLiteralTickTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("TickTime"));
    }

    private checkLiteralISOTimeStampExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: missing years and days in month validation here -- also leap seconds
        return exp.setType(this.getWellKnownType("ISOTimeStamp"));
    }

    private checkLiteralDeltaDateTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaDateTime"));
    }

    private checkLiteralDeltaPlainDateExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaPlainDate"));
    }

    private checkLiteralDeltaPlainTimeExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaPlainTime"));
    }

    private checkLiteralDeltaISOTimeStampExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaISOTimeStamp"));
    }

    private checkLiteralDeltaSecondsExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaSeconds"));
    }

    private checkLiteralDeltaTickExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaTick"));
    }

    private checkLiteralDeltaLogicalExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        return exp.setType(this.getWellKnownType("DeltaLogical"));
    }

    private checkLiteralUnicodeRegexExpression(env: TypeEnvironment, exp: LiteralRegexExpression): TypeSignature {
        //TODO: validate regex parse is error free

        return exp.setType(this.getWellKnownType("UnicodeRegex"));
    }

    private checkLiteralASCIIRegexExpression(env: TypeEnvironment, exp: LiteralRegexExpression): TypeSignature {
        //TODO: validate regex parse is error free

        if(exp.value.endsWith("a")) {
            return exp.setType(this.getWellKnownType("ASCIIRegex"));
        }
        else {
            return exp.setType(this.getWellKnownType("PathRegex"));
        }
    }

    private checkLiteralStringExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: validate string encoding is correct
        
        return exp.setType(this.getWellKnownType("String"));
    }

    private checkLiteralASCIIStringExpression(env: TypeEnvironment, exp: LiteralSimpleExpression): TypeSignature {
        //TODO: validate string encoding is correct
        
        return exp.setType(this.getWellKnownType("ASCIIString"));
    }

    private runValidatorRegex(sinfo: SourceInfo, restr: string, litstr: string): boolean {
        const res = accepts(restr, litstr);
        if(res === null) {
            this.reportError(sinfo, `Literal string failed Validator regex -- ${restr}`);
        }

        return !!res; //force to boolean
    }

    private checkValidatorRegexPack(sinfo: SourceInfo, restr: string, revalidator: RegexValidatorPack): boolean {
        if(revalidator instanceof SingleRegexValidatorPack) {
            return this.runValidatorRegex(sinfo, restr, revalidator.vre);
        }
        else if(revalidator instanceof AndRegexValidatorPack) {
            //make sure to run all of them in case one is malformed -- we want to report that
            return revalidator.validators.map((v) => this.checkValidatorRegexPack(sinfo, restr, v)).reduce((acc, v) => acc && v, true);
        }
        else if(revalidator instanceof OrRegexValidatorPack) {
            //make sure to run all of them in case one is malformed -- we want to report that
            return revalidator.validators.map((v) => this.checkValidatorRegexPack(sinfo, restr, v)).reduce((acc, v) => acc || v, false);
        }
        else {
            assert(false, "Unknown Validator regex pack type");
            return false;
        }

    }

    private checkLiteralTypedStringExpression(env: TypeEnvironment, exp: LiteralTypedStringExpression): TypeSignature {
        if(!this.checkTypeSignature(env, exp.stype)) {
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        const revalidator = this.resolver.resolveStringRegexValidatorInfo(exp.stype);
        if(this.checkError(exp.sinfo, revalidator === undefined, "Bad Validator type for StringOf")) {
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        this.checkValidatorRegexPack(exp.sinfo, exp.value.slice(1, exp.value.length - 1), revalidator as RegexValidatorPack); 
        return exp.setType(this.relations.getStringOfType(exp.stype));
    }

    private checkLiteralASCIITypedStringExpression(env: TypeEnvironment, exp: LiteralTypedStringExpression): TypeSignature {
        if(!this.checkTypeSignature(env, exp.stype)) {
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        const revalidator = this.resolver.resolveStringRegexValidatorInfo(exp.stype);
        if(this.checkError(exp.sinfo, revalidator === undefined, "Bad Validator type for ASCIIStringOf")) {
            return exp.setType(new ErrorTypeSignature(exp.stype.sinfo, undefined));
        }

        this.checkValidatorRegexPack(exp.sinfo, exp.value.slice(1, exp.value.length - 1), revalidator as RegexValidatorPack); 
        return exp.setType(this.relations.getASCIIStringOfType(exp.stype));
    }

    private checkLiteralTemplateStringExpression(env: TypeEnvironment, exp: LiteralTemplateStringExpression): TypeSignature {
        //TODO: validate string encoding is correct and extract template arguments + types
        
        return exp.setType(new StringTemplateType(exp.sinfo, "utf8", []));
    }

    private checkLiteralASCIITemplateStringExpression(env: TypeEnvironment, exp: LiteralTemplateStringExpression): TypeSignature {
        //TODO: validate string encoding is correct and extract template arguments + types
        
        return exp.setType(new StringTemplateType(exp.sinfo, "ascii", []));
    }

    private checkLiteralPathExpression(env: TypeEnvironment, exp: LiteralPathExpression): TypeSignature {
        xxxx;
    }

    private checkLiteralPathFragmentExpression(env: TypeEnvironment, exp: LiteralPathExpression): TypeSignature {
        xxxx;
    }

    private checkLiteralPathGlobExpression(env: TypeEnvironment, exp: LiteralPathExpression): TypeSignature {
        xxxx;
    }

    private checkLiteralTypeDeclValueExpression(env: TypeEnvironment, exp: LiteralTypeDeclValueExpression): TypeSignature {
        xxxx;
    }

    private checkLiteralTypeDeclIntegralValueExpression(env: TypeEnvironment, exp: LiteralTypeDeclIntegralValueExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralTypeDeclIntegralValueExpression");
    }

    private checkLiteralTypeDeclFloatPointValueExpression(env: TypeEnvironment, exp: LiteralTypeDeclFloatPointValueExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLiteralTypeDeclFloatPointValueExpression");
    }

    private checkStringSliceExpression(env: TypeEnvironment, exp: StringSliceExpression): TypeSignature {
        assert(false, "Not Implemented -- checkStringSliceExpression");
    }

    private checkASCIIStringSliceExpression(env: TypeEnvironment, exp: StringSliceExpression): TypeSignature {
        assert(false, "Not Implemented -- checkASCIIStringSliceExpression");
    }

    private checkInterpolateExpression(env: TypeEnvironment, exp: InterpolateExpression): TypeSignature {
        assert(false, "Not Implemented -- checkInterpolateExpression");
    }

    private checkHasEnvValueExpression(env: TypeEnvironment, exp: AccessEnvValueExpression): TypeSignature {
        assert(false, "Not Implemented -- checkHasEnvValueExpression");
    }
    
    private checkAccessEnvValueExpression(env: TypeEnvironment, exp: AccessEnvValueExpression): TypeSignature {
        assert(false, "Not Implemented -- checkAccessEnvValueExpression");
    }

    private checkTaskAccessInfoExpression(env: TypeEnvironment, exp: TaskAccessInfoExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskAccessInfoExpression");
    }
    
    private checkAccessNamespaceConstantExpression(env: TypeEnvironment, exp: AccessNamespaceConstantExpression): TypeSignature {
        const cdecl = this.resolver.resolveNamespaceConstant(exp.ns, exp.name);
        if(cdecl === undefined) {
            this.reportError(exp.sinfo, `Could not find namespace constant ${exp.ns}::${exp.name}`);
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        this.checkTypeSignature(env, cdecl.declaredType);
        return exp.setType(cdecl.declaredType);
    }

    private checkAccessStaticFieldExpression(env: TypeEnvironment, exp: AccessStaticFieldExpression): TypeSignature {
        assert(false, "Not Implemented -- checkAccessStaticFieldExpression");
    }

    private checkAccessVariableExpression(env: TypeEnvironment, exp: AccessVariableExpression): TypeSignature {
        if(exp.isCaptured) {
            return exp.setType(env.resolveLambdaCaptureVarType(exp.scopename) || new ErrorTypeSignature(exp.sinfo, undefined));
        }
        else {
            const vinfo = env.resolveLocalVarInfo(exp.scopename);
            if(vinfo === undefined) {
                this.reportError(exp.sinfo, `Variable ${exp.scopename} is not declared here`);
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            else {
                this.checkError(exp.sinfo, !vinfo.mustDefined, `Variable ${exp.scopename} may not be defined on all control flow paths`);
                return exp.setType(vinfo.declaredType);
            }
        }
    }

    private checkConstructorPrimaryExpression(env: TypeEnvironment, exp: ConstructorPrimaryExpression): TypeSignature {
        assert(false, "Not Implemented -- checkConstructorPrimaryExpression");
    }
    
    private checkConstructorTupleExpression(env: TypeEnvironment, exp: ConstructorTupleExpression, infertype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkConstructorTupleExpression");
    }
    
    private checkConstructorRecordExpression(env: TypeEnvironment, exp: ConstructorRecordExpression, infertype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkConstructorRecordExpression");
    }
    
    private checkConstructorEListExpression(env: TypeEnvironment, exp: ConstructorEListExpression, infertype: TypeSignature| undefined): TypeSignature {
        assert(false, "Not Implemented -- checkConstructorEListExpression");
    }

    private checkConstructorLambdaExpression(env: TypeEnvironment, exp: ConstructorLambdaExpression, infertype: TypeSignature| undefined): TypeSignature {
        assert(false, "Not Implemented -- checkConstructorLambdaExpression");
    }

    private checkLetExpression(env: TypeEnvironment, exp: LetExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLetExpression");
    }

    private checkLambdaInvokeExpression(env: TypeEnvironment, exp: LambdaInvokeExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLambdaInvokeExpression");
    }

    private checkSpecialConstructorExpression(env: TypeEnvironment, exp: SpecialConstructorExpression): TypeSignature {
        assert(false, "Not Implemented -- checkSpecialConstructorExpression");
    }

    private checkCallNamespaceFunctionExpression(env: TypeEnvironment, exp: CallNamespaceFunctionExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallNamespaceFunctionExpression");
    }

    private checkCallTypeFunctionExpression(env: TypeEnvironment, exp: CallTypeFunctionExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallTypeFunctionExpression");
    }
    
    private checkLogicActionAndExpression(env: TypeEnvironment, exp: LogicActionAndExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLogicActionAndExpression");
    }

    private checkLogicActionOrExpression(env: TypeEnvironment, exp: LogicActionOrExpression): TypeSignature {
        assert(false, "Not Implemented -- checkLogicActionOrExpression");
    }

    private checkParseAsTypeExpression(env: TypeEnvironment, exp: ParseAsTypeExpression): TypeSignature {
        assert(false, "Not Implemented -- checkParseAsTypeExpression");
    }

    ////////
    // Postfix Expressions
    private checkPostfixAccessFromIndex(env: TypeEnvironment, exp: PostfixAccessFromIndex, rcvrtype: TypeSignature): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixAccessFromIndex");
    }

    private checkPostfixProjectFromIndecies(env: TypeEnvironment, exp: PostfixProjectFromIndecies, rcvrtype: TypeSignature, expectedtype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixProjectFromIndecies");
    }

    private checkPostfixAccessFromName(env: TypeEnvironment, exp: PostfixAccessFromName, rcvrtype: TypeSignature): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixAccessFromName");
    }

    private checkPostfixProjectFromNames(env: TypeEnvironment, exp: PostfixProjectFromNames, rcvrtype: TypeSignature, expectedtype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixProjectFromNames");
    }

    private checkPostfixIsTest(env: TypeEnvironment, exp: PostfixIsTest, rcvrtype: TypeSignature): TypeSignature {
        const splits = this.processITest(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, splits.ttrue === undefined, "Test is never true");
        this.checkError(exp.sinfo, splits.tfalse === undefined, "Test is never false");

        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkPostfixAsConvert(env: TypeEnvironment, exp: PostfixAsConvert, rcvrtype: TypeSignature): TypeSignature {
        const splits = this.processITest(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, splits.ttrue === undefined, "Convert always fails");
        this.checkError(exp.sinfo, splits.tfalse === undefined, "Convert always succeeds (and is redundant)");

        return exp.setType(splits.ttrue || new ErrorTypeSignature(exp.sinfo, undefined));
    }

    private checkPostfixAssignFields(env: TypeEnvironment, exp: PostfixAssignFields, rcvrtype: TypeSignature): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixAssignFields");
    }

    private checkPostfixInvoke(env: TypeEnvironment, exp: PostfixInvoke, rcvrtype: TypeSignature): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixInvoke");
    }

    private checkPostfixLiteralKeyAccess(env: TypeEnvironment, exp: PostfixLiteralKeyAccess): TypeSignature {
        assert(false, "Not Implemented -- checkPostfixLiteralKeyAccess");
    }

    private checkPostfixOp(env: TypeEnvironment, exp: PostfixOp, expectedtype: TypeSignature | undefined): TypeSignature {
        let ctype = this.checkExpression(env, exp.rootExp, undefined);
        if(ctype instanceof ErrorTypeSignature) {
            return exp.setType(ctype);
        }

        for(let i = 0; i < exp.ops.length; ++i) {
            const op = exp.ops[i];
            const texpected = (i === exp.ops.length - 1) ? expectedtype : undefined;

            op.setRcvrType(ctype);
            switch(op.tag) {
                case PostfixOpTag.PostfixAccessFromIndex: {
                    ctype = this.checkPostfixAccessFromIndex(env, op as PostfixAccessFromIndex, ctype);
                }
                case PostfixOpTag.PostfixProjectFromIndecies: {
                    ctype = this.checkPostfixProjectFromIndecies(env, op as PostfixProjectFromIndecies, ctype, texpected);
                }
                case PostfixOpTag.PostfixAccessFromName: {
                    ctype = this.checkPostfixAccessFromName(env, op as PostfixAccessFromName, ctype);
                }
                case PostfixOpTag.PostfixProjectFromNames: {
                    ctype = this.checkPostfixProjectFromNames(env, op as PostfixProjectFromNames, ctype, texpected);
                }
                case PostfixOpTag.PostfixIsTest: {
                    ctype = this.checkPostfixIsTest(env, op as PostfixIsTest, ctype);
                }
                case PostfixOpTag.PostfixAsConvert: {
                    ctype = this.checkPostfixAsConvert(env, op as PostfixAsConvert, ctype);
                }
                case PostfixOpTag.PostfixAssignFields: {
                    ctype = this.checkPostfixAssignFields(env, op as PostfixAssignFields, ctype);
                }
                case PostfixOpTag.PostfixInvoke: {
                    ctype = this.checkPostfixInvoke(env, op as PostfixInvoke, ctype);
                }
                case PostfixOpTag.PostfixLiteralKeyAccess: {
                    ctype = this.checkPostfixLiteralKeyAccess(env, op as PostfixLiteralKeyAccess);
                }
                default: {
                    assert(op.tag === PostfixOpTag.PostfixError, "Unknown postfix op");
                    ctype = new ErrorTypeSignature(op.sinfo, undefined);
                }
            }
            op.setType(ctype);

            if(ctype instanceof ErrorTypeSignature) {
                return exp.setType(ctype);
            }
        }

        return exp.setType(ctype);
    }

    private checkPrefixNotOpExpression(env: TypeEnvironment, exp: PrefixNotOpExpression): TypeSignature {
        const etype = this.checkExpression(env, exp.exp, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return exp.setType(etype);
        }

        this.checkError(exp.sinfo, !this.relations.isBooleanType(etype, this.constraints), "Prefix Not operator requires a Bool type");
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkPrefixNegateOpExpression(env: TypeEnvironment, exp: PrefixNegateOpExpression): TypeSignature {
        const etype = this.checkExpression(env, exp.exp, undefined);
        if(etype instanceof ErrorTypeSignature) {
            return exp.setType(etype);
        }

        if(this.checkError(exp.sinfo, !this.relations.isUniqueNumericType(etype, this.constraints), "Prefix Negate operator requires a unique numeric type")) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        return exp.setType(etype);
    }

    private checkBinaryNumericArgs(env: TypeEnvironment, lhs: Expression, rhs: Expression): [boolean, TypeSignature, TypeSignature] {
        const tlhs = this.checkExpression(env, lhs, undefined);
        if(tlhs instanceof ErrorTypeSignature) {
            return [false, tlhs, tlhs];
        }

        const trhs = this.checkExpression(env, rhs, undefined);
        if(trhs instanceof ErrorTypeSignature) {
            return [false, tlhs, trhs];
        }

        if(this.checkError(lhs.sinfo, !this.relations.isUniqueNumericType(tlhs, this.constraints), "Binary operator requires a unique numeric type")) {
            return [false, tlhs, trhs];
        }
        if(this.checkError(rhs.sinfo, !this.relations.isUniqueNumericType(trhs, this.constraints), "Binary operator requires a unique numeric type")) {
            return [false, tlhs, trhs];
        }

        return [true, tlhs, trhs];
    }

    private checkBinAddExpression(env: TypeEnvironment, exp: BinAddExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        
        if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Subtraction operator requires 2 arguments of the same type")) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        return exp.setType(tlhs);
    }

    private checkBinSubExpression(env: TypeEnvironment, exp: BinSubExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Subtraction operator requires 2 arguments of the same type")) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        return exp.setType(tlhs);
    }

    private checkBinMultExpression(env: TypeEnvironment, exp: BinMultExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        let res: TypeSignature;
        if(this.relations.isPrimitiveType(tlhs, this.constraints) && this.relations.isPrimitiveType(trhs, this.constraints)) {
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Multiplication operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs;
        }
        else if(this.relations.isTypeDeclType(tlhs, this.constraints) && this.relations.isPrimitiveType(trhs, this.constraints)) {
            const baselhs = this.relations.getTypeDeclBasePrimitiveType(tlhs, this.constraints);
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(baselhs, trhs, this.constraints), "Multiplication operator requires a unit-less argument that matches underlying unit type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs
        }
        else if(this.relations.isPrimitiveType(tlhs, this.constraints) && this.relations.isTypeDeclType(trhs, this.constraints)) {
            const baserhs = this.relations.getTypeDeclBasePrimitiveType(trhs, this.constraints);
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, baserhs, this.constraints), "Multiplication operator requires a unit-less argument that matches underlying unit type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = trhs;
        }
        else {
            this.checkError(exp.sinfo, false, "Multiplication operator not allowed on 2 unit typed values");
            res = new ErrorTypeSignature(exp.sinfo, undefined);
        }

        return exp.setType(res);
    }

    private checkBinDivExpression(env: TypeEnvironment, exp: BinDivExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        let res: TypeSignature;
        if(this.relations.isPrimitiveType(tlhs, this.constraints) && this.relations.isPrimitiveType(trhs, this.constraints)) {
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Division operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs;
        }
        else if(this.relations.isTypeDeclType(tlhs, this.constraints) && this.relations.isPrimitiveType(trhs, this.constraints)) {
            const baselhs = this.relations.getTypeDeclBasePrimitiveType(tlhs, this.constraints);
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(baselhs, trhs, this.constraints), "Division operator requires a unit-less divisor argument that matches the underlying unit type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = tlhs
        }
        else if(this.relations.isTypeDeclType(tlhs, this.constraints) && this.relations.isTypeDeclType(trhs, this.constraints)) {
            if(this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Division operator requires 2 arguments of the same type")) {
                return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
            }
            res = this.relations.getTypeDeclBasePrimitiveType(trhs, this.constraints);
        }
        else {
            this.checkError(exp.sinfo, false, "Division operator not allowed on with unit typed divisor and a type-less value");
            res = new ErrorTypeSignature(exp.sinfo, undefined);
        }

        return exp.setType(res);
    }

    private checkBinKeyEqExpression(env: TypeEnvironment, exp: BinKeyEqExpression): TypeSignature {
        const lhstype = this.checkExpression(env, exp.lhs, undefined);
        const rhstype = this.checkExpression(env, exp.rhs, undefined);

        if (lhstype instanceof ErrorTypeSignature || rhstype instanceof ErrorTypeSignature) {
            return exp.setType(this.getWellKnownType("Bool"));
        }
        
        if (!this.relations.isSubtypeOf(lhstype, rhstype, this.constraints) && !this.relations.isSubtypeOf(rhstype, lhstype, this.constraints)) {
            this.reportError(exp.sinfo, `Types ${lhstype.emit(true)} and ${rhstype.emit(true)} are not comparable -- one must be subtype of the other`);
            return exp.setType(this.getWellKnownType("Bool"));
        }

        const action = this.checkValueEq(exp.lhs, lhstype, exp.rhs, rhstype);
        if (action === "err") {
            this.reportError(exp.sinfo, `Types ${lhstype.emit(true)} and ${rhstype.emit(true)} are not comparable`);
            return exp.setType(this.getWellKnownType("Bool"));
        }
        if(action === "truealways" || action === "falsealways") {
            this.reportError(exp.sinfo, `Equality operation is always ${action === "truealways" ? "true" : "false"}`);
            return exp.setType(this.getWellKnownType("Bool"));
        }
        
        if (action === "lhsnone" || action === "rhsnone" || action === "lhsnothing" || action === "rhsnothing") {
            return exp.setType(this.getWellKnownType("Bool"));
        }
        else {
            if (action === "stdkeywithunique") {
                this.checkError(exp.sinfo, !this.relations.isKeyType(lhstype, this.constraints), `left hand side of compare expression -- expected a KeyType but got ${lhstype.emit(true)}`);
                this.checkError(exp.sinfo, !this.relations.isKeyType(rhstype, this.constraints), `right hand side of compare expression -- expected a KeyType but got ${rhstype.emit(true)}`);
            }
            else if (action === "lhssomekeywithunique") {
                this.checkError(exp.sinfo, !this.relations.isKeyType(lhstype, this.constraints), `left hand side of compare expression -- expected a KeyType but got ${lhstype.emit(true)}`);
            }
            else if (action === "rhssomekeywithunique") {
                this.checkError(exp.sinfo, !this.relations.isKeyType(rhstype, this.constraints), `right hand side of compare expression -- expected a KeyType but got ${rhstype.emit(true)}`);
            }
            else {
                if (action === "lhssomekey") {
                    this.checkError(exp.sinfo, !this.relations.isKeyType(lhstype, this.constraints), `left hand side of compare expression -- expected a KeyType but got ${lhstype.emit(true)}`);
                }
                else if (action === "rhssomekey") {
                    this.checkError(exp.sinfo, !this.relations.isKeyType(rhstype, this.constraints), `right hand side of compare expression -- expected a KeyType but got ${rhstype.emit(true)}`);
                }
                else {
                    this.checkError(exp.sinfo, !this.relations.isKeyType(lhstype, this.constraints), `left hand side of compare expression -- expected a KeyType but got ${lhstype.emit(true)}`);
                    this.checkError(exp.sinfo, !this.relations.isKeyType(rhstype, this.constraints), `right hand side of compare expression -- expected a KeyType but got ${rhstype.emit(true)}`);
                }
            }

            return exp.setType(this.getWellKnownType("Bool"));
        }
    }

    private checkBinKeyNeqExpression(env: TypeEnvironment, exp: BinKeyNeqExpression): TypeSignature {
        const lhstype = this.checkExpression(env, exp.lhs, undefined);
        const rhstype = this.checkExpression(env, exp.rhs, undefined);

        if (lhstype instanceof ErrorTypeSignature || rhstype instanceof ErrorTypeSignature) {
            return exp.setType(this.getWellKnownType("Bool"));
        }
        
        if (!this.relations.isSubtypeOf(lhstype, rhstype, this.constraints) && !this.relations.isSubtypeOf(rhstype, lhstype, this.constraints)) {
            this.reportError(exp.sinfo, `Types ${lhstype.emit(true)} and ${rhstype.emit(true)} are not comparable -- one must be subtype of the other`);
            return exp.setType(this.getWellKnownType("Bool"));
        }

        const action = this.checkValueEq(exp.lhs, lhstype, exp.rhs, rhstype);
        if (action === "err") {
            this.reportError(exp.sinfo, `Types ${lhstype.emit(true)} and ${rhstype.emit(true)} are not comparable`);
            return exp.setType(this.getWellKnownType("Bool"));
        }
        if(action === "truealways" || action === "falsealways") {
            this.reportError(exp.sinfo, `Equality operation is always ${action === "truealways" ? "true" : "false"}`);
            return exp.setType(this.getWellKnownType("Bool"));
        }

        if (action === "lhsnone" || action === "rhsnone" || action === "lhsnothing" || action === "rhsnothing") {
            return exp.setType(this.getWellKnownType("Bool"));
        }
        else {
            if (action === "stdkeywithunique") {
                this.checkError(exp.sinfo, !this.relations.isKeyType(lhstype, this.constraints), `left hand side of compare expression -- expected a KeyType but got ${lhstype.emit(true)}`);
                this.checkError(exp.sinfo, !this.relations.isKeyType(rhstype, this.constraints), `right hand side of compare expression -- expected a KeyType but got ${rhstype.emit(true)}`);
            }
            else if (action === "lhssomekeywithunique") {
                this.checkError(exp.sinfo, !this.relations.isKeyType(lhstype, this.constraints), `left hand side of compare expression -- expected a KeyType but got ${lhstype.emit(true)}`);
            }
            else if (action === "rhssomekeywithunique") {
                this.checkError(exp.sinfo, !this.relations.isKeyType(rhstype, this.constraints), `right hand side of compare expression -- expected a KeyType but got ${rhstype.emit(true)}`);
            }
            else {
                if (action === "lhssomekey") {
                    this.checkError(exp.sinfo, !this.relations.isKeyType(lhstype, this.constraints), `left hand side of compare expression -- expected a KeyType but got ${lhstype.emit(true)}`);
                }
                else if (action === "rhssomekey") {
                    this.checkError(exp.sinfo, !this.relations.isKeyType(rhstype, this.constraints), `right hand side of compare expression -- expected a KeyType but got ${rhstype.emit(true)}`);
                }
                else {
                    this.checkError(exp.sinfo, !this.relations.isKeyType(lhstype, this.constraints), `left hand side of compare expression -- expected a KeyType but got ${lhstype.emit(true)}`);
                    this.checkError(exp.sinfo, !this.relations.isKeyType(rhstype, this.constraints), `right hand side of compare expression -- expected a KeyType but got ${rhstype.emit(true)}`);
                }
            }

            return exp.setType(this.getWellKnownType("Bool"));
        }
    }

    private checkNumericEqExpression(env: TypeEnvironment, exp: NumericEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator == requires 2 arguments of the same type");
        return exp.setType(this.getWellKnownType("Bool"));
    }


    private checkNumericNeqExpression(env: TypeEnvironment, exp: NumericNeqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator != requires 2 arguments of the same type");
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericLessExpression(env: TypeEnvironment, exp: NumericLessExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator < requires 2 arguments of the same type");
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericLessEqExpression(env: TypeEnvironment, exp: NumericLessEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator <= requires 2 arguments of the same type");
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericGreaterExpression(env: TypeEnvironment, exp: NumericGreaterExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator > requires 2 arguments of the same type");
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkNumericGreaterEqExpression(env: TypeEnvironment, exp: NumericGreaterEqExpression): TypeSignature {
        const [ok, tlhs, trhs] = this.checkBinaryNumericArgs(env, exp.lhs, exp.rhs);
        if(!ok) {
            return exp.setType(this.getWellKnownType("Bool"));
        }

        this.checkError(exp.sinfo, !this.relations.areSameTypes(tlhs, trhs, this.constraints), "Operator >= requires 2 arguments of the same type");
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinaryBooleanArgs(env: TypeEnvironment, lhs: Expression, rhs: Expression) {
        const tlhs = this.checkExpression(env, lhs, undefined);
        if(tlhs instanceof ErrorTypeSignature) {
            return;
        }

        const trhs = this.checkExpression(env, rhs, undefined);
        if(trhs instanceof ErrorTypeSignature) {
            return;
        }

        if(this.checkError(lhs.sinfo, !this.relations.isBooleanType(tlhs, this.constraints), "Binary operator requires a Bool type")) {
            return;
        }
        if(this.checkError(rhs.sinfo, !this.relations.isBooleanType(trhs, this.constraints), "Binary operator requires a Bool type")) {
            return;
        }

        return;
    }

    private checkBinLogicAndExpression(env: TypeEnvironment, exp: BinLogicAndExpression): TypeSignature {
        this.checkBinaryBooleanArgs(env, exp.lhs, exp.rhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinLogicOrExpression(env: TypeEnvironment, exp: BinLogicOrExpression): TypeSignature {
        this.checkBinaryBooleanArgs(env, exp.lhs, exp.rhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinLogicImpliesExpression(env: TypeEnvironment, exp: BinLogicImpliesExpression): TypeSignature {
        this.checkBinaryBooleanArgs(env, exp.lhs, exp.rhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkBinLogicIFFExpression(env: TypeEnvironment, exp: BinLogicIFFExpression): TypeSignature {
        this.checkBinaryBooleanArgs(env, exp.lhs, exp.rhs);
        return exp.setType(this.getWellKnownType("Bool"));
    }

    private checkMapEntryConstructorExpression(env: TypeEnvironment, exp: MapEntryConstructorExpression, expectedtype: TypeSignature | undefined): TypeSignature {
        assert(false, "Not Implemented -- checkMapEntryConstructorExpression");
    }

    private checkIfExpression(env: TypeEnvironment, exp: IfExpression, expectedtype: TypeSignature | undefined): TypeSignature {
        const eetype = this.checkExpression(env, exp.test.exp, undefined);
        if(eetype instanceof ErrorTypeSignature) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }

        let ttrue: TypeSignature;
        let tfalse: TypeSignature;

        if(exp.test.itestopt === undefined) {
            ttrue = this.checkExpression(env, exp.trueValue, expectedtype);
            tfalse = this.checkExpression(env, exp.falseValue, expectedtype);
        }
        else {
            const splits = this.processITest(exp.sinfo, env, eetype, exp.test.itestopt);
            this.checkError(exp.sinfo, splits.ttrue === undefined, "Test is never true -- true branch of if is unreachable");
            this.checkError(exp.sinfo, splits.tfalse === undefined, "Test is never false -- false branch of if is unreachable");

            if(exp.trueValueBinder === undefined) {
                ttrue = this.checkExpression(env, exp.trueValue, expectedtype);
            }
            else {
                const nenv = env.addLocalVariable(exp.trueValueBinder.scopename, splits.ttrue as TypeSignature, true, true);
                ttrue = this.checkExpression(nenv, exp.trueValue, expectedtype);
            }

            if(exp.falseValueBinder === undefined) {
                tfalse = this.checkExpression(env, exp.falseValue, expectedtype);
            }
            else {
                const nenv = env.addLocalVariable(exp.falseValueBinder.scopename, splits.tfalse as TypeSignature, true, true);
                tfalse = this.checkExpression(nenv, exp.falseValue, expectedtype);
            }
        }
        
        if(ttrue instanceof ErrorTypeSignature || tfalse instanceof ErrorTypeSignature) {
            return exp.setType(new ErrorTypeSignature(exp.sinfo, undefined));
        }
        else {
            const jtype = this.relations.joinTypes(ttrue, tfalse, this.constraints);
            return exp.setType(jtype);
        }
    }

    ////////
    //statement expressions
    private checkCallRefThisExpression(env: TypeEnvironment, exp: CallRefThisExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallRefThisExpression");
    }

    private checkCallRefSelfExpression(env: TypeEnvironment, exp: CallRefSelfExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallRefSelfExpression");
    }

    private checkCallTaskActionExpression(env: TypeEnvironment, exp: CallTaskActionExpression): TypeSignature {
        assert(false, "Not Implemented -- checkCallTaskActionExpression");
    }

    private checkTaskRunExpression(env: TypeEnvironment, exp: TaskRunExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskRunExpression");
    }

    private checkTaskMultiExpression(env: TypeEnvironment, exp: TaskMultiExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskMultiExpression");
    }

    private checkTaskDashExpression(env: TypeEnvironment, exp: TaskDashExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskDashExpression");
    }

    private checkTaskAllExpression(env: TypeEnvironment, exp: TaskAllExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskAllExpression");
    }

    private checkTaskRaceExpression(env: TypeEnvironment, exp: TaskRaceExpression): TypeSignature {
        assert(false, "Not Implemented -- checkTaskRaceExpression");
    }

    private checkExpression(env: TypeEnvironment, exp: Expression, expectedtype: TypeSignature | undefined): TypeSignature {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression: {
                return this.checkLiteralNoneExpression(env, exp as LiteralSingletonExpression);
            }
            case ExpressionTag.LiteralNothingExpression: {
                return this.checkLiteralNothingExpression(env, exp as LiteralSingletonExpression);
            }
            case ExpressionTag.LiteralBoolExpression: {
                return this.checkLiteralBoolExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralNatExpression: {
                return this.checkLiteralNatExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralIntExpression: {
                return this.checkLiteralIntExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralBigNatExpression: {
                return this.checkLiteralBigNatExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralBigIntExpression: {
                return this.checkLiteralBigIntExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralRationalExpression: {
                return this.checkLiteralRationalExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralFloatExpression: {
                return this.checkLiteralFloatExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDecimalExpression: {
                return this.checkLiteralDecimalExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDecimalDegreeExpression: {
                return this.checkLiteralDecimalDegreeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralLatLongCoordinateExpression: {
                return this.checkLiteralLatLongCoordinateExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralComplexNumberExpression: {
                return this.checkLiteralComplexNumberExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralByteBufferExpression: {
                return this.checkLiteralByteBufferExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUUIDv4Expression: {
                return this.checkLiteralUUIDv4Expression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUUIDv7Expression: {
                return this.checkLiteralUUIDv7Expression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralSHAContentHashExpression: {
                return this.checkLiteralSHAContentHashExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDateTimeExpression: {
                return this.checkLiteralDateTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUTCDateTimeExpression: {
                return this.checkLiteralUTCDateTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPlainDateExpression: {
                return this.checkLiteralPlainDateExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralPlainTimeExpression: {
                return this.checkLiteralPlainTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralLogicalTimeExpression: {
                return this.checkLiteralLogicalTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTickTimeExpression: {
                return this.checkLiteralTickTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralISOTimeStampExpression: {
                return this.checkLiteralISOTimeStampExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaDateTimeExpression: {
                return this.checkLiteralDeltaDateTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaPlainDateExpression: {
                return this.checkLiteralDeltaPlainDateExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaPlainTimeExpression: {
                return this.checkLiteralDeltaPlainTimeExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaISOTimeStampExpression: {
                return this.checkLiteralDeltaISOTimeStampExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaSecondsExpression: {
                return this.checkLiteralDeltaSecondsExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaTickExpression: {
                return this.checkLiteralDeltaTickExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralDeltaLogicalExpression: {
                return this.checkLiteralDeltaLogicalExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralUnicodeRegexExpression: {
                return this.checkLiteralUnicodeRegexExpression(env, exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralASCIIRegexExpression: {
                return this.checkLiteralASCIIRegexExpression(env, exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralStringExpression: {
                return this.checkLiteralStringExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralASCIIStringExpression: {
                return this.checkLiteralASCIIStringExpression(env, exp as LiteralSimpleExpression);
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
            case ExpressionTag.LiteralPathExpression: {
                return this.checkLiteralPathExpression(env, exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralPathFragmentExpression: {
                return this.checkLiteralPathFragmentExpression(env, exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralPathGlobExpression: {
                return this.checkLiteralPathGlobExpression(env, exp as LiteralPathExpression);
            }
            case ExpressionTag.LiteralTypeDeclValueExpression: {
                return this.checkLiteralTypeDeclValueExpression(env, exp as LiteralTypeDeclValueExpression);
            }
            case ExpressionTag.LiteralTypeDeclIntegralValueExpression: {
                return this.checkLiteralTypeDeclIntegralValueExpression(env, exp as LiteralTypeDeclIntegralValueExpression);
            }
            case ExpressionTag.LiteralTypeDeclFloatPointValueExpression: {
                return this.checkLiteralTypeDeclFloatPointValueExpression(env, exp as LiteralTypeDeclFloatPointValueExpression);
            }
            case ExpressionTag.StringSliceExpression: {
                return this.checkStringSliceExpression(env, exp as StringSliceExpression);
            }
            case ExpressionTag.ASCIIStringSliceExpression: {
                return this.checkASCIIStringSliceExpression(env, exp as StringSliceExpression);
            }
            case ExpressionTag.InterpolateExpression: {
                return this.checkInterpolateExpression(env, exp as InterpolateExpression);
            }
            case ExpressionTag.HasEnvValueExpression: {
                return this.checkHasEnvValueExpression(env, exp as AccessEnvValueExpression);
            }
            case ExpressionTag.AccessEnvValueExpression: {
                return this.checkAccessEnvValueExpression(env, exp as AccessEnvValueExpression);
            }
            case ExpressionTag.TaskAccessInfoExpression: {
                return this.checkTaskAccessInfoExpression(env, exp as TaskAccessInfoExpression);
            }
            case ExpressionTag.AccessNamespaceConstantExpression: {
                return this.checkAccessNamespaceConstantExpression(env, exp as AccessNamespaceConstantExpression);
            }
            case ExpressionTag.AccessStaticFieldExpression: {
                return this.checkAccessStaticFieldExpression(env, exp as AccessStaticFieldExpression);
            }
            case ExpressionTag.AccessVariableExpression: {
                return this.checkAccessVariableExpression(env, exp as AccessVariableExpression);
            }
            case ExpressionTag.ConstructorPrimaryExpression: {
                return this.checkConstructorPrimaryExpression(env, exp as ConstructorPrimaryExpression);
            }
            case ExpressionTag.ConstructorTupleExpression: {
                return this.checkConstructorTupleExpression(env, exp as ConstructorTupleExpression, expectedtype);
            }
            case ExpressionTag.ConstructorRecordExpression: {
                return this.checkConstructorRecordExpression(env, exp as ConstructorRecordExpression, expectedtype);
            }
            case ExpressionTag.ConstructorEListExpression: {
                return this.checkConstructorEListExpression(env, exp as ConstructorEListExpression, expectedtype);
            }
            case ExpressionTag.ConstructorLambdaExpression: {
                return this.checkConstructorLambdaExpression(env, exp as ConstructorLambdaExpression, expectedtype);
            }
            case ExpressionTag.LetExpression: {
                return this.checkLetExpression(env, exp as LetExpression);
            }
            case ExpressionTag.LambdaInvokeExpression: {
                return this.checkLambdaInvokeExpression(env, exp as LambdaInvokeExpression);
            }
            case ExpressionTag.SpecialConstructorExpression: {
                return this.checkSpecialConstructorExpression(env, exp as SpecialConstructorExpression);
            }
            case ExpressionTag.CallNamespaceFunctionExpression: {
                return this.checkCallNamespaceFunctionExpression(env, exp as CallNamespaceFunctionExpression);
            }
            case ExpressionTag.CallTypeFunctionExpression: {
                return this.checkCallTypeFunctionExpression(env, exp as CallTypeFunctionExpression);
            }
            case ExpressionTag.LogicActionAndExpression: {
                return this.checkLogicActionAndExpression(env, exp as LogicActionAndExpression);
            }
            case ExpressionTag.LogicActionOrExpression: {
                return this.checkLogicActionOrExpression(env, exp as LogicActionOrExpression);
            }
            case ExpressionTag.ParseAsTypeExpression: {
                return this.checkParseAsTypeExpression(env, exp as ParseAsTypeExpression);
            }
            case ExpressionTag.PostfixOpExpression: {
                return this.checkPostfixOp(env, exp as PostfixOp, expectedtype);
            }
            case ExpressionTag.PrefixNotOpExpression: {
                return this.checkPrefixNotOpExpression(env, exp as PrefixNotOpExpression);
            }
            case ExpressionTag.PrefixNegateOpExpression: {
                return this.checkPrefixNegateOpExpression(env, exp as PrefixNegateOpExpression);
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
                return this.checkBinKeyEqExpression(env, exp as BinKeyEqExpression);
            }
            case ExpressionTag.BinKeyNeqExpression: {
                return this.checkBinKeyNeqExpression(env, exp as BinKeyNeqExpression);
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
                return this.checkBinLogicAndExpression(env, exp as BinLogicAndExpression);
            }
            case ExpressionTag.BinLogicOrExpression: {
                return this.checkBinLogicOrExpression(env, exp as BinLogicOrExpression);
            }
            case ExpressionTag.BinLogicImpliesExpression: {
                return this.checkBinLogicImpliesExpression(env, exp as BinLogicImpliesExpression);
            }
            case ExpressionTag.BinLogicIFFExpression: {
                return this.checkBinLogicIFFExpression(env, exp as BinLogicIFFExpression);
            }
            case ExpressionTag.MapEntryConstructorExpression: {
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, expectedtype);
            }
            case ExpressionTag.IfExpression: {
                return this.checkIfExpression(env, exp as IfExpression, expectedtype);
            }
            default: {
                assert(exp.tag === ExpressionTag.ErrorExpression, "Unknown expression kind");
                return new ErrorTypeSignature(exp.sinfo, undefined);
            }
        }
    }

    private checkExpressionRHS(env: TypeEnvironment, exp: Expression, expectedtype: TypeSignature | undefined): TypeSignature {
        xxxx; //other RHS options here

        return this.checkExpression(env, exp, expectedtype);
    }

    /*
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
                accepts = tirtypedecl.strvalidator.vre.acceptsString(extractLiteralStringValue(litval.expstr, true), this.m_assembly.m_literalRegexs);
            }
            else {
                accepts = tirtypedecl.strvalidator.vre.acceptsString(extractLiteralASCIIStringValue(litval.expstr, true), this.m_assembly.m_literalRegexs);
            }
            this.raiseErrorIf(exp.sinfo, !accepts, "literal string does not satisfy validator constraint");
        }

        if (tirtypedecl.pthvalidator !== undefined) {
            const litval = (lexp[0] as TIRLiteralValue).exp;
            let accepts = false;
            if (tirtypedecl.pthvalidator.kind === "path") {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPath(extractLiteralStringValue(litval.expstr, true));
            }
            else if (tirtypedecl.pthvalidator.kind === "pathfragment") {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPathFragment(extractLiteralStringValue(litval.expstr, true));
            }
            else {
                accepts = tirtypedecl.pthvalidator.vpth.acceptsPathGlob(extractLiteralASCIIStringValue(litval.expstr, true));
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

    private checkAccessEnvValue(env: ExpressionTypeEnvironment, exp: AccessEnvValueExpression): ExpressionTypeEnvironment {
        this.raiseErrorIf(exp.sinfo, !this.m_taskOpsOk || this.m_taskSelfOk !== "write", `Can only access "environment" variables in task actions`);

        const valtype = this.normalizeTypeOnly(exp.valtype, env.binds);
        const restype = this.normalizeTypeOnly(new UnionTypeSignature(exp.sinfo, [exp.valtype, new NominalTypeSignature(exp.sinfo, "Core", ["None"])]), env.binds);

        return env.setResultExpressionInfo(new TIRAccessEnvValueExpression(exp.sinfo, exp.keyname, this.toTIRTypeKey(valtype), this.toTIRTypeKey(restype), exp.orNoneMode), restype);
    }

    private checkAccessStaticField(env: ExpressionTypeEnvironment, exp: AccessStaticFieldExpression): ExpressionTypeEnvironment {
        const oftype = this.normalizeTypeOnly(exp.stype, env.binds);
        const cmf = this.resolveMemberConst(exp.sinfo, oftype, exp.name);
        this.raiseErrorIf(exp.sinfo, cmf === undefined, `const ${exp.name} not defined on type ${oftype.typeID}`);

        const cdecl = (cmf as OOMemberLookupInfo<StaticMemberDecl>);
        this.raiseErrorIf(exp.sinfo, (cdecl.decl.value as ConstantExpressionValue).captured.size !== 0, "Expression uses unbound variables");

        const tirdecltype = this.toTIRTypeKey(cdecl.ttype);
        const rtype = this.normalizeTypeOnly(cdecl.decl.declaredType, TemplateBindScope.createBaseBindScope(cdecl.oobinds));
        
        if (cdecl.ootype.attributes.includes("__enum_type")) {
            this.m_pendingConstMemberDecls.push(cdecl);
            return env.setResultExpressionInfo(new TIRAccessConstMemberFieldExpression(exp.sinfo, tirdecltype, exp.name, this.toTIRTypeKey(rtype)), rtype);
        }
        else {
            const cexp = this.compileTimeReduceConstantExpression((cdecl.decl.value as ConstantExpressionValue).exp, env.binds);

            if (cexp !== undefined) {
                return this.emitCoerceIfNeeded(this.checkExpression(env, cexp, rtype), exp.sinfo, rtype);
            }
            else {
                this.m_pendingConstMemberDecls.push(cdecl);
                return env.setResultExpressionInfo(new TIRAccessConstMemberFieldExpression(exp.sinfo, tirdecltype, exp.name, this.toTIRTypeKey(rtype)), rtype);
            }
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
    */

    private checkEmptyStatement(env: TypeEnvironment, stmt: EmptyStatement): TypeEnvironment {
        return env;
    }

    private checkVariableDeclarationStatement(env: TypeEnvironment, stmt: VariableDeclarationStatement): TypeEnvironment {
        this.checkTypeSignature(env, stmt.vtype);
        
        return env.addLocalVariable(stmt.name, stmt.vtype, false, false);
    }
    
    private checkVariableMultiDeclarationStatement(env: TypeEnvironment, stmt: VariableMultiDeclarationStatement): TypeEnvironment {
        for(let i = 0; i < stmt.decls.length; ++i) {
            this.checkTypeSignature(env, stmt.decls[i].vtype);
            env = env.addLocalVariable(stmt.decls[i].name, stmt.decls[i].vtype, false, false);
        }
        return env;
    }

    private checkVariableInitializationStatement(env: TypeEnvironment, stmt: VariableInitializationStatement): TypeEnvironment {
        this.checkTypeSignature(env, stmt.vtype);

        const itype = !(stmt.vtype instanceof AutoTypeSignature) ? stmt.vtype : undefined;
        const rhs = this.checkExpressionRHS(env, stmt.exp, itype);
        
        //TODO: do we need to update any other type env info here based on RHS actions???

        this.checkError(stmt.sinfo, itype !== undefined && !(rhs instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(rhs, itype, this.constraints), `Expression of type ${(itype as TypeSignature).emit(true)} cannot be assigned to variable of type ${stmt.vtype.emit(true)}`);
        return env.addLocalVariable(stmt.name, itype || rhs, stmt.isConst, true); //try to recover a bit
    }

    private checkVariableMultiInitializationStatement(env: TypeEnvironment, stmt: VariableMultiInitializationStatement): TypeEnvironment {
        for(let i = 0; i < stmt.decls.length; ++i) {
            this.checkTypeSignature(env, stmt.decls[i].vtype);
        }

        const iopts = stmt.decls.map((decl) => !(decl.vtype instanceof AutoTypeSignature) ? decl.vtype : undefined);

        let evals: TypeSignature[] = [];
        if(!Array.isArray(stmt.exp)) {
            const iinfer = iopts.some((opt) => opt === undefined) ? undefined : new EListTypeSignature(stmt.sinfo, iopts as TypeSignature[]);    
            const etype = this.checkExpressionRHS(env, stmt.exp, iinfer);
            if(etype instanceof EListTypeSignature) {
                evals.push(...etype.entries);
            }
            else {
                this.reportError(stmt.sinfo, "Expected a EList for multi-variable initialization");
            }
        }
        else {
            for(let i = 0; i < stmt.exp.length; ++i) {
                const etype = this.checkExpressionRHS(env, stmt.exp[i], i < iopts.length ? iopts[i] : undefined); //undefined out-of-bounds is ok here
                evals.push(etype);
            }
        }

        this.checkError(stmt.sinfo, iopts.length !== evals.length, "Mismatch in number of variables and expressions in multi-variable initialization");
        for(let i = evals.length; i < iopts.length; ++i) {
            evals.push(new ErrorTypeSignature(stmt.sinfo, undefined)); //try to recover a bit
        }

        for(let i = 0; i < stmt.decls.length; ++i) {
            const decl = stmt.decls[i];
            const itype = iopts[i];
            const etype = evals[i];

            this.checkError(stmt.sinfo, itype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, itype, this.constraints), `Expression of type ${(itype as TypeSignature).emit(true)} cannot be assigned to variable of type ${etype.emit(true)}`);
            env = env.addLocalVariable(decl.name, itype || etype, stmt.isConst, true); //try to recover a bit
        }

        return env;
    }

    private checkVariableAssignmentStatement(env: TypeEnvironment, stmt: VariableAssignmentStatement): TypeEnvironment {
        const vinfo = env.resolveLocalVarInfo(stmt.name);
        if(vinfo === undefined) {
            this.reportError(stmt.sinfo, `Variable ${stmt.name} is not declared`);
            return env;
        }

        this.checkError(stmt.sinfo, !vinfo.isConst, `Variable ${stmt.name} is declared as const and cannot be assigned`);

        const rhs = this.checkExpressionRHS(env, stmt.exp, vinfo.declaredType);
        this.checkError(stmt.sinfo, !this.relations.isSubtypeOf(rhs, vinfo.declaredType, this.constraints), `Expression of type ${rhs.emit(true)} cannot be assigned to variable of type ${vinfo.declaredType.emit(true)}`);

        return env.assignLocalVariable(stmt.name);
    }

    private checkVariableMultiAssignmentStatement(env: TypeEnvironment, stmt: VariableMultiAssignmentStatement): TypeEnvironment {
        const opts = stmt.names.map((vname) => env.resolveLocalVarInfo(vname));
        for(let i = 0; i < opts.length; ++i) {
            if(opts[i] !== undefined) {
                this.checkError(stmt.sinfo, (opts[i] as VarInfo).isConst, `Variable ${stmt.names[i]} is declared as const and cannot be assigned`);
            }
            else {
                this.reportError(stmt.sinfo, `Variable ${stmt.names[i]} is not declared`);
            }
        }

        let evals: TypeSignature[] = [];
        if(!Array.isArray(stmt.exp)) {
            const iinfer = opts.some((opt) => opt === undefined) ? undefined : new EListTypeSignature(stmt.sinfo, opts.map((opt) => (opt as VarInfo).declaredType));    
            const etype = this.checkExpressionRHS(env, stmt.exp, iinfer);
            if(etype instanceof EListTypeSignature) {
                evals.push(...etype.entries);
            }
            else {
                this.reportError(stmt.sinfo, "Expected a EList for multi-variable initialization");
            }
        }
        else {
            for(let i = 0; i < stmt.exp.length; ++i) {
                const etype = this.checkExpressionRHS(env, stmt.exp[i], (i < opts.length && opts[i] !== undefined) ? (opts[i] as VarInfo).declaredType : undefined);
                evals.push(etype);
            }
        }

        this.checkError(stmt.sinfo, opts.length !== evals.length, "Mismatch in number of variables and expressions in multi-variable initialization");
        for(let i = evals.length; i < opts.length; ++i) {
            evals.push(new ErrorTypeSignature(stmt.sinfo, undefined)); //try to recover a bit
        }

        for(let i = 0; i < stmt.names.length; ++i) {
            const name = stmt.names[i];
            const itype = opts[i] !== undefined ? (opts[i] as VarInfo).declaredType : undefined;
            const etype = evals[i];

            this.checkError(stmt.sinfo, itype !== undefined && !(etype instanceof ErrorTypeSignature) && !this.relations.isSubtypeOf(etype, itype, this.constraints), `Expression of type ${(itype as TypeSignature).emit(true)} cannot be assigned to variable of type ${etype.emit(true)}`);
            env = env.assignLocalVariable(name);
        }

        return env;
    }

    private checkVariableRetypeStatement(env: TypeEnvironment, stmt: VariableRetypeStatement): TypeEnvironment {
        const vinfo = env.resolveLocalVarInfo(stmt.name);
        if(vinfo === undefined) {
            this.reportError(stmt.sinfo, `Variable ${stmt.name} is not declared`);
            return env;
        }

        const splits = this.processITest(stmt.sinfo, env, vinfo.declaredType, stmt.ttest);
        this.checkError(stmt.sinfo, splits.ttrue === undefined, `retype will always fail`);

        return env.retypeLocalVariable(stmt.name, splits.ttrue || vinfo.declaredType);
    }

    private checkReturnStatement(env: TypeEnvironment, stmt: ReturnStatement): TypeEnvironment {
        if(stmt.value === undefined) {
            xxxx;
        }
        else if(!Array.isArray(stmt.value)) {
            xxxx;
        }
        else {  
            xxxx;
        }
    }

    private checkIfElseStatement(env: TypeEnvironment, stmt: IfStatement): TypeEnvironment {
        xxxx;
    }

    private checkSwitchStatement(env: TypeEnvironment, stmt: SwitchStatement): TypeEnvironment {
        xxxx;
    }

    private checkMatchStatement(env: TypeEnvironment, stmt: MatchStatement): TypeEnvironment {
        xxxx;
    }

    private checkAbortStatement(env: TypeEnvironment, stmt: AbortStatement): TypeEnvironment {
        xxxx;
    }

    private checkAssertStatement(env: TypeEnvironment, stmt: AssertStatement): TypeEnvironment {
        xxxx;
    }

    private checkValidateStatement(env: TypeEnvironment, stmt: ValidateStatement): TypeEnvironment {
        xxxx;
    }

    private checkDebugStatement(env: TypeEnvironment, stmt: DebugStatement): TypeEnvironment {
        this.checkExpression(env, stmt.value, undefined);

        return env;
    }

    private checkStandaloneExpressionStatement(env: TypeEnvironment, stmt: StandaloneExpressionStatement): TypeEnvironment {
        assert(false, "Not implemented -- StandaloneExpressionStatement");
    }

    private checkThisUpdateStatement(env: TypeEnvironment, stmt: ThisUpdateStatement): TypeEnvironment {
        assert(false, "Not implemented -- ThisUpdateStatement");
    }

    private checkSelfUpdateStatement(env: TypeEnvironment, stmt: SelfUpdateStatement): TypeEnvironment {
        assert(false, "Not implemented -- SelfUpdateStatement");
    }

    private checkEnvironmentUpdateStatement(env: TypeEnvironment, stmt: EnvironmentUpdateStatement): TypeEnvironment {
        assert(false, "Not implemented -- EnvironmentUpdateStatement");
    }

    private checkEnvironmentBracketStatement(env: TypeEnvironment, stmt: EnvironmentBracketStatement): TypeEnvironment {
        assert(false, "Not implemented -- EnvironmentBracketStatement");
    }

    private checkTaskStatusStatement(env: TypeEnvironment, stmt: TaskStatusStatement): TypeEnvironment {
        assert(false, "Not implemented -- TaskStatusStatement");
    }

    private checkTaskEventEmitStatement(env: TypeEnvironment, stmt: TaskEventEmitStatement): TypeEnvironment {
        assert(false, "Not implemented -- TaskEventEmitStatement");
    }

    private checkTaskYieldStatement(env: TypeEnvironment, stmt: TaskYieldStatement): TypeEnvironment {
        assert(false, "Not implemented -- TaskYieldStatement");
    }

    private checkBlockStatement(env: TypeEnvironment, stmt: BlockStatement): TypeEnvironment {
        for (let i = 0; i < stmt.statements.length; ++i) {
            env = this.checkStatement(env, stmt.statements[i]);
        }

        return env;
    }

    /*
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
        vrl.sort((a, b) => ((a.vname !== b.vname) ? (a.vname < b.vname ? -1 : 1) : 0));

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
*/

    private checkStatement(env: TypeEnvironment, stmt: Statement): TypeEnvironment {
        if(!env.hasNormalFlow()) {
            this.reportError(stmt.sinfo, "Unreachable code");
            return env;
        }

        switch(stmt.tag) {
            case StatementTag.EmptyStatement: {
                return this.checkEmptyStatement(env, stmt as EmptyStatement);
            }
            case StatementTag.VariableDeclarationStatement: {
                return this.checkVariableDeclarationStatement(env, stmt as VariableDeclarationStatement);
            }
            case StatementTag.VariableMultiDeclarationStatement: {
                return this.checkVariableMultiDeclarationStatement(env, stmt as VariableMultiDeclarationStatement);
            }
            case StatementTag.VariableInitializationStatement: {
                return this.checkVariableInitializationStatement(env, stmt as VariableInitializationStatement);
            }
            case StatementTag.VariableMultiInitializationStatement: {
                return this.checkVariableMultiInitializationStatement(env, stmt as VariableMultiInitializationStatement);
            }
            case StatementTag.VariableAssignmentStatement: {
                return this.checkVariableAssignmentStatement(env, stmt as VariableAssignmentStatement);
            }
            case StatementTag.VariableMultiAssignmentStatement: {
                return this.checkVariableMultiAssignmentStatement(env, stmt as VariableMultiAssignmentStatement);
            }
            case StatementTag.VariableRetypeStatement: {
                return this.checkVariableRetypeStatement(env, stmt as VariableRetypeStatement);
            }
            case StatementTag.ReturnStatement: {
                return this.checkReturnStatement(env, stmt as ReturnStatement);
            }
            case StatementTag.IfElseStatement: {
                return this.checkIfElseStatement(env, stmt as IfStatement);
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
            case StatementTag.ValidateStatement: {
                return this.checkValidateStatement(env, stmt as ValidateStatement);
            }
            case StatementTag.DebugStatement: {
                return this.checkDebugStatement(env, stmt as DebugStatement);
            }
            case StatementTag.StandaloneExpressionStatement: {
                return this.checkStandaloneExpressionStatement(env, stmt as StandaloneExpressionStatement);
            }
            case StatementTag.ThisUpdateStatement: {
                return this.checkThisUpdateStatement(env, stmt as ThisUpdateStatement);
            }
            case StatementTag.SelfUpdateStatement: {
                return this.checkSelfUpdateStatement(env, stmt as SelfUpdateStatement);
            }
            case StatementTag.EnvironmentUpdateStatement: {
                return this.checkEnvironmentUpdateStatement(env, stmt as EnvironmentUpdateStatement);
            }
            case StatementTag.EnvironmentBracketStatement: {
                return this.checkEnvironmentBracketStatement(env, stmt as EnvironmentBracketStatement);
            }
            case StatementTag.TaskStatusStatement: {
                return this.checkTaskStatusStatement(env, stmt as TaskStatusStatement);
            }
            case StatementTag.TaskEventEmitStatement: {
                return this.checkTaskEventEmitStatement(env, stmt as TaskEventEmitStatement);
            }
            case StatementTag.TaskYieldStatement: {
                return this.checkTaskYieldStatement(env, stmt as TaskYieldStatement);
            }
            case StatementTag.BlockStatement: {
                return this.checkBlockStatement(env, stmt as BlockStatement);
            }
            default: {
                assert(stmt.tag === StatementTag.ErrorStatement, `Unknown statement kind -- ${stmt.tag}`);

                return env;
            }
        }
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
            let rargs: Map<string, VarInfo> = new Map<string, VarInfo>(args);

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

            fargs.push(new TIRFunctionParameter("$return", this.toTIRTypeKey(this.normalizeTypeOnly(invk.resultType, binds))));
            rargs.set("$return", new VarInfo(this.normalizeTypeOnly(invk.resultType, binds), true, true));

            if(optthistype !== undefined && invk.isThisRef) {
                fargs.push(new TIRFunctionParameter("$this", this.toTIRTypeKey(optthistype)));
                rargs.set("$this", new VarInfo(optthistype, true, true));
            }

            const env = ExpressionTypeEnvironment.createInitialEnvForEvalWArgsAndPCodeArgs(binds, argpcodes, rargs);
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

    processSamples(invk: InvokeDecl): [TIRInvokeSampleDeclInline[], TIRInvokeSampleDeclFile[]] {
        let inline: TIRInvokeSampleDeclInline[] = [];
        invk.samples.filter((sm) => sm instanceof InvokeSampleDeclInline).forEach((sm) => {
            const ism = sm as InvokeSampleDeclInline;
            inline.push(new TIRInvokeSampleDeclInline(ism.sinfo, ism.istest, ism.args, ism.output));
        });

        let file: TIRInvokeSampleDeclFile[] = [];
        invk.samples.filter((sm) => sm instanceof InvokeSampleDeclFile).forEach((sm) => {
            const fsm = sm as InvokeSampleDeclFile;
            file.push(new TIRInvokeSampleDeclFile(fsm.sinfo, fsm.istest, fsm.filepath));
        });

        return [inline, file];
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
        tdecl.memberFields.forEach((mf) => {
            const fkey = TIRIDGenerator.generateMemberFieldID(tkey, mf.name);
            const decltype = this.toTIRTypeKey(this.normalizeTypeOnly(mf.declaredType, TemplateBindScope.createEmptyBindScope()));

            const tirmf = new TIRMemberFieldDecl(fkey, tkey, mf.name, mf.sourceLocation, mf.srcFile, mf.attributes, decltype);
            this.m_tirFieldMap.set(fkey, tirmf);
        });

        //if this is a non-universal and non-template concept then we need to also process all of the subtypes!!!
        if(!ResolvedType.isUniversalConceptType(rtype) && tdecl.terms.length === 0) {
            const estl = this.m_assembly.getAllEntities()
            .map((ee) => this.createResolvedTypeForEntityDeclExportable(ee))
            .filter((ee) =>  ee !== undefined && this.atomSubtypeOf(ee, rtype)) as ResolvedEntityAtomType[];
            
            estl.forEach((est) => {
                this.toTIRTypeKey(ResolvedType.createSingle(est));
            });
        }
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

    private processNamespaceFunctionInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvoke {
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
        const [smapleinline, samplefile] = this.processSamples(invoke);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(ibinds), argpcodes, fargs);

        const bbimpl = invoke.body as BodyImplementation;
        if(bbimpl.body instanceof SynthesisBody) {
            const inv = new TIRInvokeSynthesis(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, false, false, false, false, params, false, restype, preconds, postconds, smapleinline, samplefile);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
        else {
            const body = this.checkBodyStatement(invoke.srcFile, env, bbimpl.body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(ibinds)), false, "no");
            const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, false, false, false, false, params, false, restype, preconds, postconds, smapleinline, samplefile, body);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
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
        
        const preconds = this.processPrecondition(invoke, undefined, TemplateBindScope.createEmptyBindScope(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), fargs, invoke.preconditions);
        const postconds = this.processPostcondition(invoke, undefined, TemplateBindScope.createEmptyBindScope(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), fargs, invoke.postconditions);
        const [smapleinline, samplefile] = this.processSamples(invoke);

        if(invoke.body === undefined) {
            const inv = new TIRInvokeAbstractDeclaration(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, new Map<string, TIRTypeKey>(), new Map<string, TIRPCodeKey>(), false, true, params, false, restype, preconds, postconds, smapleinline, samplefile);
            
            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
        else {
            this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
            const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createEmptyBindScope(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), fargs);

            const bbimpl = invoke.body as BodyImplementation;
            if(bbimpl.body instanceof SynthesisBody) {
                const inv = new TIRInvokeSynthesis(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, new Map<string, TIRTypeKey>(), new Map<string, TIRPCodeKey>(), false, false, true, false, params, false, restype, preconds, postconds, smapleinline, samplefile);

                this.m_tirInvokeMap.set(invkey, inv);
                return inv;
            }
            else {
                const body = this.checkBodyStatement(invoke.srcFile, env, bbimpl.body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()), false, "no");
                const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, new Map<string, TIRTypeKey>(), new Map<string, TIRPCodeKey>(), false, false, true, false, params, false, restype, preconds, postconds, smapleinline, samplefile, body);

                this.m_tirInvokeMap.set(invkey, inv);
                return inv;
            }
        }
    }

    private processNamespaceOperatorImplInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl): TIRInvoke {
        this.checkInvokeDecl(invoke.startSourceLocation, invoke);
        this.raiseErrorIf(invoke.startSourceLocation, invoke.terms.length !== 0, "cannot have template parameters on operators");

        const recursive = invoke.recursive === "yes";

        let fargs: Map<string, VarInfo> = new Map<string, VarInfo>();
        let params: TIRFunctionParameter[] = [];
        invoke.params.forEach((ff) => {
            const ptype = this.normalizeTypeOnly(ff.type, TemplateBindScope.createEmptyBindScope());
            let plit: TIRLiteralValue | undefined = undefined;
            if (ff.ddlit !== undefined) {
                const ll = this.reduceLiteralValueToCanonicalForm(ff.ddlit.exp, TemplateBindScope.createEmptyBindScope());
                this.raiseErrorIf(invoke.startSourceLocation, ll[0] === undefined, "literal value could not be resolved for parameter");

                plit = ll[0];
            }

            fargs.set(ff.name, new VarInfo(ptype, true, true));
            params.push(new TIRFunctionParameter(ff.name, this.toTIRTypeKey(ptype), plit));
        });

        const restype = this.toTIRTypeKey(this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
        this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.length !== 0 || invoke.postconditions.length !== 0, "pre/post conditions not supported on operators yet");

        this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.length !== 0 || invoke.postconditions.length !== 0, "pre/post conditions cannot be applied on concrete operators -- that implicitly restricts the way the virtual operator can be used!");
        const [smapleinline, samplefile] = this.processSamples(invoke);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createEmptyBindScope(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), fargs);

        const bbimpl = invoke.body as BodyImplementation;
        if (bbimpl.body instanceof SynthesisBody) {
            const inv = new TIRInvokeSynthesis(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, new Map<string, TIRTypeKey>(), new Map<string, TIRPCodeKey>(), false, false, true, false, params, false, restype, [], [], smapleinline, samplefile);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;

        }
        else {
            const body = this.checkBodyStatement(invoke.srcFile, env, bbimpl.body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createEmptyBindScope()), false, "no");
            const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, new Map<string, TIRTypeKey>(), new Map<string, TIRPCodeKey>(), false, false, true, false, params, false, restype, [], [], smapleinline, samplefile, body);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
    }

    private processMemberFunctionInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvoke {
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
        const [smapleinline, samplefile] = this.processSamples(invoke);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs);

        const bbimpl = invoke.body as BodyImplementation;
        if (bbimpl.body instanceof SynthesisBody) {
            const inv = new TIRInvokeSynthesis(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, false, false, false, false, params, false, restype, preconds, postconds, smapleinline, samplefile);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
        else {
            const body = this.checkBodyStatement(invoke.srcFile, env, bbimpl.body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, "no");
            const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, false, false, false, false, params, false, restype, preconds, postconds, smapleinline, samplefile, body);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
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
        const [smapleinline, samplefile] = this.processSamples(invoke);

        const inv = new TIRInvokeAbstractDeclaration(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, false, params, false, restype, preconds, postconds, smapleinline, samplefile);

        this.m_tirInvokeMap.set(invkey, inv);
        return inv;
    }

    private processMemberMethodVirtualDeclInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvoke {
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
        const [smapleinline, samplefile] = this.processSamples(invoke);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs);

        const bbimpl = invoke.body as BodyImplementation;
        if (bbimpl.body instanceof SynthesisBody) {
            const inv = new TIRInvokeSynthesis(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, true, false, false, params, false, restype, preconds, postconds, smapleinline, samplefile);
    
            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
        else {
            const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, this.m_taskSelfOk);
            const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, true, false, false, params, false, restype, preconds, postconds, smapleinline, samplefile, body);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
    }

    private processMemberMethodVirtualImplInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], declaredecl: [ResolvedType, InvokeDecl, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvoke {
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

        this.raiseErrorIf(invoke.startSourceLocation, invoke.preconditions.length !== 0 || invoke.postconditions.length !== 0, "pre/post conditions cannot be applied on concrete operators -- that implicitly restricts the way the virtual operator can be used!");
        const [smapleinline, samplefile] = this.processSamples(invoke);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs);

        const bbimpl = invoke.body as BodyImplementation;
        if (bbimpl.body instanceof SynthesisBody) {
            const inv = new TIRInvokeSynthesis(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, true, false, false, params, false, restype, [], [], smapleinline, samplefile);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;

        }
        else {
            const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), false, this.m_taskSelfOk);
            const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, true, false, false, params, false, restype, [], [], smapleinline, samplefile, body);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
    }

    private processMemberMethodImplInvokeInfo(name: string, invkey: TIRInvokeKey, invoke: InvokeDecl, enclosingdecl: [ResolvedType, OOPTypeDecl, Map<string, ResolvedType>], ibinds: Map<string, ResolvedType>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>): TIRInvoke {
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
        const [smapleinline, samplefile] = this.processSamples(invoke);

        this.checkArgsAndResultTypes(invoke.startSourceLocation, fargs, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)));
        const env = StatementTypeEnvironment.createInitialEnvForStdBodyEval(TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds), argpcodes, fargs);

        const bbimpl = invoke.body as BodyImplementation;
        if (bbimpl.body instanceof SynthesisBody) {
            const inv = new TIRInvokeSynthesis(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, false, false, false, params, invoke.isThisRef, restype, preconds, postconds, smapleinline, samplefile);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
        else {
            const body = this.checkBodyStatement(invoke.srcFile, env, (invoke.body as BodyImplementation).body as ScopedBlockStatement, this.normalizeTypeOnly(invoke.resultType, TemplateBindScope.createBaseBindScope(enclosingdecl[2]).pushScope(ibinds)), this.m_taskOpsOk, this.m_taskSelfOk);
            const inv = new TIRInvokeImplementation(invkey, name, invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, true, false, false, false, params, invoke.isThisRef, restype, preconds, postconds, smapleinline, samplefile, body);

            this.m_tirInvokeMap.set(invkey, inv);
            return inv;
        }
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

        const inv = new TIRInvokeImplementation(codepack.invk, "lambda", invoke.startSourceLocation, invoke.endSourceLocation, invoke.srcFile, invoke.attributes, recursive, tbinds, tirpcodes, false, false, false, true, params, false, restype, [], [], [], [], body);

        this.m_tirInvokeMap.set(codepack.invk, inv);
        return inv;
    }

    ensureTIRNamespaceDecl(ns: string): TIRNamespaceDeclaration {
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
        this.toTIRTypeKey(this.getSpecialUUIDv4Type());
        this.toTIRTypeKey(this.getSpecialUUIDv7Type());
        this.toTIRTypeKey(this.getSpecialSHAContentHashType());
        this.toTIRTypeKey(this.getSpecialRegexType());
        this.toTIRTypeKey(this.getSpecialNothingType());
        this.toTIRTypeKey(this.getSpecialTaskIDType());

        this.toTIRTypeKey(this.getSpecialAnyConceptType());
        this.toTIRTypeKey(this.getSpecialSomeConceptType());

        this.toTIRTypeKey(this.getSpecialKeyTypeConceptType());
        this.toTIRTypeKey(this.getSpecialValidatorConceptType());
        this.toTIRTypeKey(this.getSpecialPathValidatorConceptType());

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
    }

    static processAssembly(asm: Assembly, buildlevel: BuildLevel, exportvals: {ns: string, fname: string}[]): { tasm: TIRAssembly | undefined, errors: string[], aliasmap: Map<string, string> } {
        let tchecker = new TypeChecker(asm, buildlevel);

        //Must always have Core namespace and special types registered -- even if just as default values
        tchecker.m_tirNamespaceMap.set("Core", new TIRNamespaceDeclaration("Core"));
        tchecker.processSpecialTypes();

        asm.getNamespaces().forEach((nsdecl) => {
            tchecker.ensureTIRNamespaceDecl(nsdecl.ns);
        });

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

        if(tchecker.m_errors.length !== 0) {
            return { tasm: undefined, errors: tchecker.m_errors.map((ee) => `${ee[2]} -- ${ee[1]} @ ${ee[0]}`), aliasmap: new Map<TIRTypeKey, TIRTypeKey>() };
        }
        else {
            return { tasm: new TIRAssembly(tchecker.m_tirNamespaceMap, tchecker.m_tirTypeMap, tchecker.m_tirFieldMap, tchecker.m_tirInvokeMap, tchecker.m_tirCodePackMap, asm.m_literalRegexs, asm.m_literalPaths), errors: [], aliasmap: new Map<TIRTypeKey, TIRTypeKey>([...tchecker.m_typedefResolutions].map((rr) => [rr[0], rr[1].typeID])) };
        }
    }

    static generateTASM(pckge: PackageConfig[], buildLevel: BuildLevel, entrypoints: {ns: string, fname: string}[], depsmap: Map<string, string[]>): { tasm: TIRAssembly | undefined, errors: string[], aliasmap: Map<string, string> } {
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
                    return { tasm: undefined, errors: ["Hard failure in parse of namespace deps"], aliasmap: new Map<TIRTypeKey, TIRTypeKey>() };
                }

                if(deps.ns !== "Core") {
                    deps.deps.push("Core");
                }

                const nsnamemap = ["Core", deps.ns, ...[...deps.remap].map((rrp) => rrp[0])];
                filetonsnamemap.set(fe[1], new Set<string>(nsnamemap));

                if(!depsmap.has(deps.ns)) {
                    depsmap.set(deps.ns, []);
                }
                let ddm = depsmap.get(deps.ns) as string[];
                deps.deps.forEach((dep) => {
                    if(!ddm.includes(dep)) {
                        ddm.push(dep);
                    }
                });
                ddm.sort();

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
                    return { tasm: undefined, errors: ["Cyclic dependency in namespaces or misspelled import namespace"], aliasmap: new Map<TIRTypeKey, TIRTypeKey>() };
                }

                const nns = nsopts[0];
                const nsfiles = nsfilemap.get(nns) as [PackageConfig, string, string, string][];

                for (let i = 0; i < nsfiles.length; ++i) {
                    const parseok = p.parseCompilationUnitPass1(nsfiles[i][1], nsfiles[i][3], nsfiles[i][0].macrodefs);
                    if (!parseok || p.getParseErrors() !== undefined) {
                        const parseErrors = p.getParseErrors();
                        if (parseErrors !== undefined) {
                            return { tasm: undefined, errors: parseErrors.map((err: [string, number, string]) => JSON.stringify(err)), aliasmap: new Map<TIRTypeKey, TIRTypeKey>() };
                        }
                    }
                }
    
                for (let i = 0; i < nsfiles.length; ++i) {
                    const parseok = p.parseCompilationUnitPass2(nsfiles[i][1], nsfiles[i][3], nsfiles[i][0].macrodefs, filetonsnamemap.get(nsfiles[i][1]) as Set<string>);
                    if (!parseok || p.getParseErrors() !== undefined) {
                        const parseErrors = p.getParseErrors();
                        if (parseErrors !== undefined) {
                            return { tasm: undefined, errors: parseErrors.map((err: [string, number, string]) => JSON.stringify(err)), aliasmap: new Map<TIRTypeKey, TIRTypeKey>() };
                        }
                    }
                }

                allfe = [...allfe, ...nsfiles].sort((a, b) => ((a[1] !== b[1]) ? (a[1] < b[1] ? -1 : 1) : 0));
                nsdone.add(nns);
            }
        }
        catch (ex) {
            return { tasm: undefined, errors: [`Hard failure in parse with exception -- ${ex}`], aliasmap: new Map<TIRTypeKey, TIRTypeKey>() };
        }

        //
        //TODO: compute hash of sources here -- maybe bundle for debugging or something too?
        //

        return TypeChecker.processAssembly(assembly, buildLevel, entrypoints);
    }
}

export { TypeError, TypeChecker };
