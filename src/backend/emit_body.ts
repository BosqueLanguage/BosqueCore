import assert from "node:assert";

import { JSCodeFormatter } from "./enitter_support.js";
import { Expression, ExpressionTag, LiteralSimpleExpression } from "../frontend/body.js";

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
        return "[NOT IMPLEMENTED]";
    }

    private emitLiteralIntExpression(exp: LiteralSimpleExpression): string {
        return "[NOT IMPLEMENTED]";
    }

    private emitLiteralBigNatExpression(exp: LiteralSimpleExpression): string {
        return "[NOT IMPLEMENTED]";
    }

    private emitLiteralBigIntExpression(exp: LiteralSimpleExpression): string {
        return "[NOT IMPLEMENTED]";
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
            /*
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
            case ExpressionTag.LiteralExRegexExpression: {
                return this.checkLiteralExRegexExpression(env, exp as LiteralRegexExpression);
            }
            case ExpressionTag.LiteralStringExpression: {
                return this.checkLiteralStringExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralExStringExpression: {
                return this.checkLiteralExStringExpression(env, exp as LiteralSimpleExpression);
            }
            case ExpressionTag.LiteralTypedStringExpression: {
                return this.checkLiteralTypedStringExpression(env, exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralExTypedStringExpression: {
                return this.checkLiteralExTypedStringExpression(env, exp as LiteralTypedStringExpression);
            }
            case ExpressionTag.LiteralTemplateStringExpression: {
                return this.checkLiteralTemplateStringExpression(env, exp as LiteralTemplateStringExpression);
            }
            case ExpressionTag.LiteralTemplateExStringExpression: {
                return this.checkLiteralTemplateExStringExpression(env, exp as LiteralTemplateStringExpression);
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
