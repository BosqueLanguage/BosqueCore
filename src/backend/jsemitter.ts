import assert from "node:assert";

import { JSCodeFormatter } from "./jsemitter_support.js";
import { AccessEnvValueExpression, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, CallNamespaceFunctionExpression, CallTypeFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, ConstructorPrimaryExpression, ConstructorRecordExpression, ConstructorTupleExpression, Expression, ExpressionTag, ITest, ITestErr, ITestLiteral, ITestNone, ITestNothing, ITestOk, ITestSome, ITestSomething, ITestType, InterpolateExpression, LambdaInvokeExpression, LetExpression, LiteralPathExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTemplateStringExpression, LiteralTypeDeclFloatPointValueExpression, LiteralTypeDeclIntegralValueExpression, LiteralTypeDeclValueExpression, LiteralTypedStringExpression, LogicActionAndExpression, LogicActionOrExpression, ParseAsTypeExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAsConvert, PostfixAssignFields, PostfixInvoke, PostfixIsTest, PostfixLiteralKeyAccess, PostfixOp, PostfixOpTag, PostfixProjectFromIndecies, PostfixProjectFromNames, PostfixTypeDeclValue, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, SpecialConstructorExpression, TaskAccessInfoExpression } from "../frontend/body.js";
import { TypeCheckerRelations } from "../frontend/checker_relations.js";
import { TemplateConstraintScope, TypeSignature } from "../frontend/type.js";

class JSEmitter {
    readonly fmt: JSCodeFormatter;
    readonly relations: TypeCheckerRelations;

    constructor(relations: TypeCheckerRelations) {
        this.fmt = new JSCodeFormatter(0);
        this.relations = relations;
    }

    private emitITest_None(val: string, isnot: boolean): string {
        return `${val}.$is${isnot ? "Not" : ""}None()`;
    }

    private emitITest_Some(val: string, isnot: boolean): string {
        return `${val}.$is${isnot ? "Not" : ""}Some()`;
    }

    private emitITest_Nothing(val: string, isnot: boolean): string {
        return `${val}.$is${isnot ? "Not" : ""}Nothing()`;
    }

    private emitITest_Something(val: string, isnot: boolean): string {
        return `${val}.$is${isnot ? "Not" : ""}Something()`;
    }

    private emitITest_Ok(val: string, isnot: boolean): string {
        return `${val}.$is${isnot ? "Not" : ""}Ok()`;
    }

    private emitITest_Err(val: string, isnot: boolean): string {
        return `${val}.$is${isnot ? "Not" : ""}Err()`;
    }

    private emitITest_Literal(val: string, literal: string, isnot: boolean): string{
        return `${val}.$is${isnot ? "Not" : ""}KeyEqual(${literal})`;
    }

    private emitITest_Type(val: string, oftype: TypeSignature, isnot: boolean): string {
        const ttype = this.relations.normalizeTypeSignatureIncludingTemplate(oftype, this.tconstraints);
        const nns = ttype.;

        return `${val}.$is${isnot ? "Not" : ""}SubTypeOf(${xxxx})`;
    }
    
    private processITest(val: string, tt: ITest, tconstraints: TemplateConstraintScope): string {
        if(tt instanceof ITestType) {
            return this.emitITest_Type(val, tt.ttype, tt.isnot);
        }
        else if(tt instanceof ITestLiteral) {
            const ll = this.emitExpression(tt.literal.exp, true);
            return this.emitITest_Literal(val, ll, tt.isnot);
        }
        else {
            if(tt instanceof ITestNone) {
                return this.emitITest_None(val, tt.isnot);
            }
            else if(tt instanceof ITestSome) {
                return this.emitITest_Some(val, tt.isnot);
            }
            else if(tt instanceof ITestNothing) {
                return this.emitITest_Nothing(val, tt.isnot);
            }
            else if(tt instanceof ITestSomething) {
                return this.emitITest_Something(val, tt.isnot);
            }
            else if(tt instanceof ITestOk) {
                return this.emitITest_Ok(val, tt.isnot);
            }
            else {
                assert(tt instanceof ITestErr, "missing case in ITest");
                return this.emitITest_Err(val, tt.isnot);
            }
        }
    }

    private emitLiteralNoneExpression(): string {
        return "$Runtime.none";
    }

    private emitLiteralNothingExpression() {
        return "$Runtime.nothing";
    }

    private emitLiteralBoolExpression(exp: LiteralSimpleExpression): string {
        return exp.value === "true" ? "$Runtime.true" : "$Runtime.false";
    }

    private emitLiteralNatExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.nat(${exp.value.slice(0, -1)}n)`;
    }

    private emitLiteralIntExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.int(${exp.value.slice(0, -1)}n)`;
    }

    private emitLiteralBigNatExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.bignat(${exp.value.slice(0, -1)}n)`;
    }

    private emitLiteralBigIntExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.bigint(${exp.value.slice(0, -1)}n)`;
    }

    private emitLiteralRationalExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented -- Rational");
    }

    private emitLiteralFloatExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.float(${exp.value}.slice(0, -1))`;
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
        return `$Runtime.regex(${exp.value})`;
    }
    
    private emitLiteralCRegexExpression(exp: LiteralRegexExpression): string {
        return `$Runtime.regex(${exp.value})`;
    }
    
    private emitLiteralStringExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.string(${exp.value})`;
    }
    
    private emitLiteralCStringExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.cstring(${exp.value})`;
    }
    
    private emitLiteralTypedStringExpression(exp: LiteralTypedStringExpression): string {
        assert(false, "Not implemented -- TypedString");
    }
    
    private emitLiteralExTypedStringExpression(exp: LiteralTypedStringExpression): string {
        assert(false, "Not implemented -- ExTypedString");
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
        return `${exp.ns.ns.join(".")}.${exp.name}()`;
    }
    
    private emitAccessStaticFieldExpression(exp: AccessStaticFieldExpression): string {
        assert(false, "Not implemented -- AccessStaticField");
    }
    
    private emitAccessVariableExpression(exp: AccessVariableExpression): string {
        if(!exp.isCaptured) {
            return exp.scopename;
        }
        else {
            return `$lambda.${exp.scopename}`;
        }
    }
    
    private emitConstructorPrimaryExpression(exp: ConstructorPrimaryExpression): string {
        assert(false, "Not implemented -- ConstructorPrimary");
    }
    
    private emitConstructorTupleExpression(exp: ConstructorTupleExpression): string {
        assert(false, "Not implemented -- ConstructorTuple");
    }
    
    private emitConstructorRecordExpression(exp: ConstructorRecordExpression): string {
        assert(false, "Not implemented -- ConstructorRecord");
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
        assert(false, "Not implemented -- CallNamespaceFunction");
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

    private emitPostfixAccessFromIndex(exp: PostfixAccessFromIndex): string {
        assert(false, "Not Implemented -- checkPostfixAccessFromIndex");
    }

    private emitPostfixProjectFromIndecies(exp: PostfixProjectFromIndecies): string {
        assert(false, "Not Implemented -- checkPostfixProjectFromIndecies");
    }

    private emitPostfixAccessFromName(exp: PostfixAccessFromName): string {
        assert(false, "Not Implemented -- checkPostfixAccessFromName");
    }

    private emitPostfixProjectFromNames(exp: PostfixProjectFromNames): string {
        assert(false, "Not Implemented -- checkPostfixProjectFromNames");
    }

    private emitPostfixIsTest(exp: PostfixIsTest): string {
        const oftype = this.relations.normalizeTypeSignatureIncludingTemplate(exp.ttype, this.tconstraints);
        
        const splits = this.processITest(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, splits.ttrue === undefined, "Test is never true");
        this.checkError(exp.sinfo, splits.tfalse === undefined, "Test is never false");

        return exp.setType(this.getWellKnownType("Bool"));
    }

    private emitPostfixAsConvert(exp: PostfixAsConvert): string {
        const splits = this.processITest(exp.sinfo, env, rcvrtype, exp.ttest);
        this.checkError(exp.sinfo, splits.ttrue === undefined, "Convert always fails");
        //if always true then this is an upcast and OK!

        return exp.setType(splits.ttrue || new ErrorTypeSignature(exp.sinfo, undefined));
    }

    private emitPostfixTypeDeclValue(exp: PostfixTypeDeclValue): string {
        if(exp.opr === "value") {
            const vtype = this.relations.getTypeDeclValueType(rcvrtype, this.constraints);
            return exp.setType(vtype || new ErrorTypeSignature(exp.sinfo, undefined));
        }
        else {
            const btype = this.relations.getTypeDeclBasePrimitiveType(rcvrtype, this.constraints);
            return exp.setType(btype || new ErrorTypeSignature(exp.sinfo, undefined));
        }
    }

    private emitPostfixAssignFields(exp: PostfixAssignFields): string {
        assert(false, "Not Implemented -- checkPostfixAssignFields");
    }

    private emitPostfixInvoke(exp: PostfixInvoke): string {
        assert(false, "Not Implemented -- checkPostfixInvoke");
    }

    private emitPostfixLiteralKeyAccess(exp: PostfixLiteralKeyAccess): string {
        assert(false, "Not Implemented -- checkPostfixLiteralKeyAccess");
    }

    private emitPostfixOp(exp: PostfixOp, toplevel: boolean): string {
        let eexp = this.emitExpression(exp.rootExp, false);
    
        for(let i = 0; i < exp.ops.length; ++i) {
            const op = exp.ops[i];
            
            switch(op.tag) {
                case PostfixOpTag.PostfixAccessFromIndex: {
                    eexp += this.emitPostfixAccessFromIndex(op as PostfixAccessFromIndex);
                }
                case PostfixOpTag.PostfixProjectFromIndecies: {
                    eexp += this.emitPostfixProjectFromIndecies(op as PostfixProjectFromIndecies);
                }
                case PostfixOpTag.PostfixAccessFromName: {
                    eexp += this.emitPostfixAccessFromName(op as PostfixAccessFromName);
                }
                case PostfixOpTag.PostfixProjectFromNames: {
                    eexp += this.emitPostfixProjectFromNames(op as PostfixProjectFromNames);
                }
                case PostfixOpTag.PostfixIsTest: {
                    eexp += this.emitPostfixIsTest(op as PostfixIsTest);
                }
                case PostfixOpTag.PostfixAsConvert: {
                    eexp += this.emitPostfixAsConvert(op as PostfixAsConvert);
                }
                case PostfixOpTag.PostfixTypeDeclValue: {
                    eexp += this.emitPostfixTypeDeclValue(op as PostfixTypeDeclValue);
                }
                case PostfixOpTag.PostfixAssignFields: {
                    eexp += this.emitPostfixAssignFields(op as PostfixAssignFields);
                }
                case PostfixOpTag.PostfixInvoke: {
                    eexp += this.emitPostfixInvoke(op as PostfixInvoke);
                }
                case PostfixOpTag.PostfixLiteralKeyAccess: {
                    eexp += this.emitPostfixLiteralKeyAccess(op as PostfixLiteralKeyAccess);
                }
                default: {
                    assert(op.tag === PostfixOpTag.PostfixError, "Unknown postfix op");
                    eexp += "[ERROR POSTFIX OP]";
                }
            }
        }

        return eexp;
    }

    private emitPrefixNotOpExpression(exp: PrefixNotOpExpression): string {
        return `!${this.emitExpression(exp.exp, false)}`;
    }

    private emitPrefixNegateOrPlusOpExpression(exp: PrefixNegateOrPlusOpExpression): string {
        return `${exp.op}${this.emitExpression(exp.exp, false)}`;
    }

    emitExpression(exp: Expression, toplevel: boolean): string {
        switch (exp.tag) {
            case ExpressionTag.LiteralNoneExpression: {
                return this.emitLiteralNoneExpression();
            }
            case ExpressionTag.LiteralNothingExpression: {
                return this.emitLiteralNothingExpression();
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
            case ExpressionTag.LiteralExTypedStringExpression: {
                return this.emitLiteralExTypedStringExpression(exp as LiteralTypedStringExpression);
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
                return this.emitConstructorPrimaryExpression(exp as ConstructorPrimaryExpression);
            }
            case ExpressionTag.ConstructorTupleExpression: {
                return this.emitConstructorTupleExpression(exp as ConstructorTupleExpression);
            }
            case ExpressionTag.ConstructorRecordExpression: {
                return this.emitConstructorRecordExpression(exp as ConstructorRecordExpression);
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
            /*
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
                return this.checkMapEntryConstructorExpression(env, exp as MapEntryConstructorExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.IfExpression: {
                return this.checkIfExpression(env, exp as IfExpression, typeinfer);
            }
            */
            default: {
                assert(exp.tag === ExpressionTag.ErrorExpression, "Unknown expression kind");
                return "[ERROR EXPRESSION]";
            }
        }
    }

    /*
    private checkExpressionRHS(env: TypeEnvironment, exp: Expression, typeinfer: TypeInferContext | undefined): TypeSignature {
        const ttag = exp.tag;
        switch (ttag) {
            case ExpressionTag.CallRefThisExpression: {
                return this.checkCallRefThisExpression(env, exp as CallRefThisExpression);
            }
            case ExpressionTag.CallRefSelfExpression: {
                return this.checkCallRefSelfExpression(env, exp as CallRefSelfExpression);
            }
            case ExpressionTag.CallTaskActionExpression: {
                return this.checkCallTaskActionExpression(env, exp as CallTaskActionExpression);
            }
            case ExpressionTag.TaskRunExpression: {
                return this.checkTaskRunExpression(env, exp as TaskRunExpression);
            }
            case ExpressionTag.TaskMultiExpression: {
                return this.checkTaskMultiExpression(env, exp as TaskMultiExpression);
            }
            case ExpressionTag.TaskDashExpression: {
                return this.checkTaskDashExpression(env, exp as TaskDashExpression);
            }
            case ExpressionTag.TaskAllExpression: {
                return this.checkTaskAllExpression(env, exp as TaskAllExpression);
            }
            case ExpressionTag.TaskRaceExpression: {
                return this.checkTaskRaceExpression(env, exp as TaskRaceExpression);
            }
            default: {
                return this.checkExpression(env, exp, typeinfer);
            }
        }
    }
    */
}

export {
    BodyEmitter
};
