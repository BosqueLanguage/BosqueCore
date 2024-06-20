import assert from "node:assert";

import { JSCodeFormatter } from "./enitter_support.js";
import { AccessEnvValueExpression, Expression, ExpressionTag, InterpolateExpression, LiteralPathExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralTemplateStringExpression, LiteralTypeDeclFloatPointValueExpression, LiteralTypeDeclIntegralValueExpression, LiteralTypeDeclValueExpression, LiteralTypedStringExpression, TaskAccessInfoExpression } from "../frontend/body.js";

class BodyEmitter {
    readonly fmt: JSCodeFormatter;

    constructor(iidnt: number) {
        this.fmt = new JSCodeFormatter(iidnt);
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
        assert(false, "Not implemented");
    }

    private emitLiteralFloatExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.float(${exp.value}.slice(0, -1))`;
    }
    
    private emitLiteralDecimalExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDecimalDegreeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralLatLongCoordinateExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralComplexNumberExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralByteBufferExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralUUIDv4Expression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralUUIDv7Expression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralSHAContentHashExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDateTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralUTCDateTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralPlainDateExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralPlainTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralLogicalTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralTickTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralISOTimeStampExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDeltaDateTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDeltaPlainDateExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDeltaPlainTimeExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDeltaISOTimeStampExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDeltaSecondsExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDeltaTickExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralDeltaLogicalExpression(exp: LiteralSimpleExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralUnicodeRegexExpression(exp: LiteralRegexExpression): string {
        return `$Runtime.regex(${exp.value})`;
    }
    
    private emitLiteralExRegexExpression(exp: LiteralRegexExpression): string {
        return `$Runtime.regex(${exp.value})`;
    }
    
    private emitLiteralStringExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.string(${exp.value})`;
    }
    
    private emitLiteralExStringExpression(exp: LiteralSimpleExpression): string {
        return `$Runtime.exstring(${exp.value})`;
    }
    
    private emitLiteralTypedStringExpression(exp: LiteralTypedStringExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralExTypedStringExpression(exp: LiteralTypedStringExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralTemplateStringExpression(exp: LiteralTemplateStringExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralTemplateExStringExpression(exp: LiteralTemplateStringExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralPathExpression(exp: LiteralPathExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralPathFragmentExpression(exp: LiteralPathExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralPathGlobExpression(exp: LiteralPathExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralTypeDeclValueExpression(exp: LiteralTypeDeclValueExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralTypeDeclIntegralValueExpression(exp: LiteralTypeDeclIntegralValueExpression): string {
        assert(false, "Not implemented");
    }
    
    private emitLiteralTypeDeclFloatPointValueExpression(exp: LiteralTypeDeclFloatPointValueExpression): string {
        assert(false, "Not implemented");
    }

    private emitInterpolateExpression(exp: InterpolateExpression): string {
        assert(false, "Not implemented");
    }
        
    private emitHasEnvValueExpression(exp: AccessEnvValueExpression): string {
        assert(false, "Not implemented");
    }
            
    private emitAccessEnvValueExpression(exp: AccessEnvValueExpression): string {
        assert(false, "Not implemented");
    }
            
    private emitTaskAccessInfoExpression(exp: TaskAccessInfoExpression): string {
        assert(false, "Not implemented");
    }

    emitExpression(exp: Expression): string {
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
            case ExpressionTag.LiteralExRegexExpression: {
                return this.emitLiteralExRegexExpression(exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralStringExpression: {
                return this.emitLiteralStringExpression(exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralExStringExpression: {
                return this.emitLiteralExStringExpression(exp as LiteralSimpleExpression);
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
            case ExpressionTag.LiteralTemplateExStringExpression: {
                return this.emitLiteralTemplateExStringExpression(exp as LiteralTemplateStringExpression);
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
                return this.emitLiteralTypeDeclValueExpression(exp as LiteralTypeDeclValueExpression);
            }
            case ExpressionTag.LiteralTypeDeclIntegralValueExpression: {
                return this.emitLiteralTypeDeclIntegralValueExpression(exp as LiteralTypeDeclIntegralValueExpression);
            }
            case ExpressionTag.LiteralTypeDeclFloatPointValueExpression: {
                return this.emitLiteralTypeDeclFloatPointValueExpression(exp as LiteralTypeDeclFloatPointValueExpression);
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
            /*
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
                return this.checkConstructorTupleExpression(env, exp as ConstructorTupleExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.ConstructorRecordExpression: {
                return this.checkConstructorRecordExpression(env, exp as ConstructorRecordExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.ConstructorEListExpression: {
                return this.checkConstructorEListExpression(env, exp as ConstructorEListExpression, TypeInferContext.asSimpleType(typeinfer));
            }
            case ExpressionTag.ConstructorLambdaExpression: {
                return this.checkConstructorLambdaExpression(env, exp as ConstructorLambdaExpression, TypeInferContext.asSimpleType(typeinfer));
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
                return this.checkPostfixOp(env, exp as PostfixOp, typeinfer);
            }
            case ExpressionTag.PrefixNotOpExpression: {
                return this.checkPrefixNotOpExpression(env, exp as PrefixNotOpExpression);
            }
            case ExpressionTag.PrefixNegateOrPlusOpExpression: {
                return this.checkPrefixNegateOrPlusOpExpression(env, exp as PrefixNegateOrPlusOpExpression);
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
