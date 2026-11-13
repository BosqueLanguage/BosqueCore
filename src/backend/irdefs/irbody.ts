import { IRSourceInfo } from "./irsupport.js";
import { IREListTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature } from "./irtype.js";

import assert from "node:assert";

enum IRExpressionTag {
    IRLiteralNoneExpression = "IRLiteralNoneExpression",
    IRLiteralBoolExpression = "IRLiteralBoolExpression",
    
    IRLiteralNatExpression = "IRLiteralNatExpression",
    IRLiteralIntExpression = "IRLiteralIntExpression",
    IRLiteralChkNatExpression = "IRLiteralChkNatExpression",
    IRLiteralChkIntExpression = "IRLiteralChkIntExpression",
    IRLiteralRationalExpression = "IRLiteralRationalExpression",
    IRLiteralFloatExpression = "IRLiteralFloatExpression",
    IRLiteralDecimalExpression = "IRLiteralDecimalExpression",
    IRLiteralDecimalDegreeExpression = "IRLiteralDecimalDegreeExpression",
    IRLiteralLatLongCoordinateExpression = "IRLiteralLatLongCoordinateExpression",
    IRLiteralComplexExpression = "IRLiteralComplexExpression",

    IRLiteralByteBufferExpression = "IRLiteralByteBufferExpression",
    IRLiteralUUIDv4Expression = "IRLiteralUUIDv4Expression",
    IRLiteralUUIDv7Expression = "IRLiteralUUIDv7Expression",
    IRLiteralSHAContentHashExpression = "IRLiteralSHAContentHashExpression",

    IRLiteralTZDateTimeExpression = "IRLiteralTZDateTimeExpression",
    IRLiteralTAITimeExpression = "IRLiteralTAITimeExpression",
    IRLiteralPlainDateExpression = "IRLiteralPlainDateExpression",
    IRLiteralPlainTimeExpression = "IRLiteralPlainTimeExpression",
    IRLiteralLogicalTimeExpression = "IRLiteralLogicalTimeExpression",
    IRLiteralISOTimeStampExpression = "IRLiteralISOTimeStampExpression",
    IRLiteralDeltaDateTimeExpression = "IRLiteralDeltaDateTimeExpression",
    IRLiteralDeltaISOTimeStampExpression = "IRLiteralDeltaISOTimeStampExpression",
    IRLiteralDeltaSecondsExpression = "IRLiteralDeltaSecondsExpression",
    IRLiteralDeltaLogicalTimeExpression = "IRLiteralDeltaLogicalTimeExpression",

    IRLiteralUnicodeRegexExpression = "IRLiteralUnicodeRegexExpression",
    IRLiteralCRegexExpression = "IRLiteralCRegexExpression",

    IRLiteralByteExpression = "IRLiteralByteExpression",
    IRLiteralCCharExpression = "IRLiteralCCharExpression",
    IRLiteralUnicodeCharExpression = "IRLiteralUnicodeCharExpression",

    IRLiteralCStringExpression = "IRLiteralCStringExpression",
    IRLiteralStringExpression = "IRLiteralStringExpression",

    IRLiteralFormatStringExpression = "IRLiteralFormatStringExpression",
    IRLiteralFormatCStringExpression = "IRLiteralFormatCStringExpression",

    //TODO: path literal options here

    //TODO: path literal -format- options here

    IRLiteralTypedExpression = "IRLiteralTypedExpression",
    IRLiteralTypedStringExpression = "IRLiteralTypedStringExpression",
    IRLiteralTypedCStringExpression = "IRLiteralTypedCStringExpression",

    //TODO: path typed literal and -format- options here

    IRAccessEnvHasExpression = "IRAccessEnvHasExpression",
    IRAccessEnvGetExpression = "IRAccessEnvGetExpression",
    IRAccessEnvTryGetExpression = "IRAccessEnvTryGetExpression",

    IRTaskAccessIDExpression = "IRTaskAccessIDExpression",
    IRTaskAccessParentIDExpression = "IRTaskAccessParentIDExpression",

    IRAccessConstantExpression = "IRAccessConstantExpression",
    IRAccessEnumExpression = "IRAccessEnumExpression",

    IRAccessParameterVariableExpression = "IRAccessParameterVariableExpression",
    IRAccessLocalVariableExpression = "IRAccessLocalVariableExpression",
    IRAccessCapturedVariableExpression = "IRAccessCapturedVariableExpression",
    IRAccessTempVariableExpression = "IRAccessTempVariableExpression",

    IRAccessTypeDeclValueExpression = "IRAccessTypeDeclValueExpression",
    IRConstructSafeTypeDeclExpression = "IRConstructSafeTypeDeclExpression",
    
    IRConstructorSomeTypeExpression = "IRConstructorSomeTypeExpression",
    IRConstructorOkTypeExpression = "IRConstructorOkTypeExpression",
    IRConstructorFailTypeExpression = "IRConstructorFailTypeExpression",
    IRConstructorAPISuccessTypeExpression = "IRConstructorAPISuccessTypeExpression",
    IRConstructorMapEntryTypeExpression = "IRConstructorMapEntryTypeExpression",

    IRConstructorStandardEntityExpression = "IRConstructorStandardEntityExpression",
    IRConstructorLambdaExpression = "IRConstructorLambdaExpression",
    IRConstructorEListExpression = "IRConstructorEListExpression",

    IRConstructorListEmptyExpression = "IRConstructorListEmptyExpression",
    IRConstructorListPassthroughExpression = "IRConstructorListPassthroughExpression",
    IRConstructorListSingletonsExpression = "IRConstructorListSingletonsExpression",
    IRConstructorListMixedExpression = "IRConstructorListMixedExpression",

    IRConstructorMapEmptyExpression = "IRConstructorMapEmptyExpression",
    IRConstructorMapSingletonsExpression = "IRConstructorMapSingletonsExpression",

    IRAccessFieldSpecialExpression = "IRAccessFieldSpecialExpression",
    IRAccessFieldDirectExpression = "IRAccessFieldDirectExpression",
    IRAccessFieldVirtualExpression = "IRAccessFieldVirtualExpression",

    IRAccessEListIndexExpression = "IRAccessEListIndexExpression",

    IRInvokeSimpleExpression = "IRInvokeSimpleExpression",
    IRInvokeSimpleWithImplicitsExpression = "IRInvokeSimpleWithImplicitsExpression",
    IRInvokeVirtualSimpleExpression = "IRInvokeVirtualSimpleExpression",
    IRInvokeVirtualWithImplicitsExpression = "IRInvokeVirtualWithImplicitsExpression",

    IRInvokeCallAgentOrAPIExpression = "IRInvokeCallAgentOrAPIExpression",
    IRInvokeTaskActionExpression = "IRInvokeTaskActionExpression",

    IRInterpolateFormatCStringExpression = "IRInterpolateFormatCStringExpression",
    IRInterpolateFormatStringExpression = "IRInterpolateFormatStringExpression",

    IRPrefixNotOpExpression = "IRPrefixNotOpExpression",
    IRPrefixNegateOpExpression = "IRPrefixNegateOrPlusOpExpression",
    IRPrefixPlusOpExpression = "IRPrefixPlusOpExpression",

    IRBinAddExpression = "IRBinAddExpression",
    IRBinSubExpression = "IRBinSubExpression",
    IRBinMultExpression = "IRBinMultExpression",
    IRBinDivExpression = "IRBinDivExpression",

    IRNumericEqExpression = "IRNumericEqExpression",
    IRNumericNeqExpression = "IRNumericNeqExpression",
    IRNumericLessExpression = "IRNumericLessExpression",
    IRNumericLessEqExpression = "IRNumericLessEqExpression",
    IRNumericGreaterExpression = "IRNumericGreaterExpression",
    IRNumericGreaterEqExpression = "IRNumericGreaterEqExpression",

    IRIsNoneOptionExpression = "IRIsNoneOptionExpression",
    IRIsNotNoneOptionExpression = "IRIsNotNoneOptionExpression",
    IRIsOptionEqValueExpression = "IRIsOptionEqValueExpression",
    IRIsOptionNeqValueExpression = "IRIsOptionNeqValueExpression",
    IRIsSomeEqValueExpression = "IRIsSomeEqValueExpression",
    IRIsSomeNeqValueExpression = "IRIsSomeNeqValueExpression",

    IRBinKeyEqDirectExpression = "IRBinKeyEqDirectExpression",
    IRBinKeyNeqDirectExpression = "IRBinKeyNeqDirectExpression",
    IRBinKeyLessDirectExpression = "IRBinKeyLessDirectExpression",

    IRLogicAndExpression = "IRLogicAndExpression",
    IRLogicOrExpression = "IRLogicOrExpression",

    IRLogicSimpleConditionalExpression = "IRLogicSimpleConditionalExpression",

    IRLiteralOptionOfNoneExpression = "IRLiteralOptionOfNoneExpression",
    IRConstructOptionFromSomeExpression = "IRConstructOptionFromSomeExpression",
    IRExtractSomeFromOptionExpression = "IRExtractSomeFromOptionExpression",
    IRExtractSomeValueFromOptionExpression = "IRExtractSomeValueFromOptionExpression",

    IRConstructResultFromOkExpression = "IRConstructResultFromOkExpression",
    IRConstructResultFromFailExpression = "IRConstructResultFromFailExpression",
    IRExtractOkFromResultExpression = "IRExtractOkFromResultExpression",
    IRExtractOkValueFromResultExpression = "IRExtractOkValueFromResultExpression",
    IRExtractFailFromResultExpression = "IRExtractFailFromResultExpression",
    IRExtractFailValueFromResultExpression = "IRExtractFailValueFromResultExpression",

    IRIsConceptRepresentationOfTypeExpression = "IRIsConceptRepresentationOfTypeExpression",
    IRIsNotConceptRepresentationOfTypeExpression = "IRIsNotConceptRepresentationOfTypeExpression",
    IRIsConceptRepresentationSubtypeOfTypeExpression = "IRIsConceptRepresentationSubtypeOfTypeExpression",
    IRIsNotConceptRepresentationSubtypeOfTypeExpression = "IRIsNotConceptRepresentationSubtypeOfTypeExpression",

    IRStaticIsTypeSubtypeOfExpression = "IRStaticIsTypeSubtypeOfExpression",

    IRBoxEntityToConceptRepresentationExpression = "IRBoxEntityToConceptRepresentationExpression",
    IRUnboxEntityFromConceptRepresentationExpression = "IRUnboxEntityFromConceptRepresentationExpression",
    IRConvertConceptRepresentationExpression = "IRConvertConceptRepresentationExpression"
}

abstract class IRExpression {
    readonly tag: IRExpressionTag;

    constructor(tag: IRExpressionTag) {
        this.tag = tag;
    }

    abstract isSimpleExpression(): boolean;

    static jsonEmit_IRExpression(expr: IRExpression): [string, object] {
        if(expr instanceof IRLiteralNoneExpression) {
            return ["LiteralNoneExpression", IRLiteralNoneExpression.jsonEmit_IRLiteralNoneExpression(expr)];
        }
        else if(expr instanceof IRLiteralBoolExpression) {
            return ["LiteralBoolExpression", IRLiteralBoolExpression.jsonEmit_IRLiteralBoolExpression(expr)];
        }
        
        else if(expr instanceof IRLiteralNatExpression) {
            return ["LiteralNatExpression", IRLiteralNatExpression.jsonEmit_IRLiteralNatExpression(expr)];
        }
        else if(expr instanceof IRLiteralIntExpression) {
            return ["LiteralIntExpression", IRLiteralIntExpression.jsonEmit_IRLiteralIntExpression(expr)];
        }
        else if(expr instanceof IRLiteralChkNatExpression) {
            return ["LiteralChkNatExpression", IRLiteralChkNatExpression.jsonEmit_IRLiteralChkNatExpression(expr)];
        }
        else if(expr instanceof IRLiteralChkIntExpression) {
            return ["LiteralChkIntExpression", IRLiteralChkIntExpression.jsonEmit_IRLiteralChkIntExpression(expr)];
        }
        else if(expr instanceof IRLiteralRationalExpression) {
            return ["LiteralRationalExpression", IRLiteralRationalExpression.jsonEmit_IRLiteralRationalExpression(expr)];
        }
        else if(expr instanceof IRLiteralFloatExpression) {
            return ["LiteralFloatExpression", IRLiteralFloatExpression.jsonEmit_IRLiteralFloatExpression(expr)];
        }
        else if(expr instanceof IRLiteralDecimalExpression) {
            return ["LiteralDecimalExpression", IRLiteralDecimalExpression.jsonEmit_IRLiteralDecimalExpression(expr)];
        }
        else if(expr instanceof IRLiteralDecimalDegreeExpression) {
            return ["LiteralDecimalDegreeExpression", IRLiteralDecimalDegreeExpression.jsonEmit_IRLiteralDecimalDegreeExpression(expr)];
        }
        else if(expr instanceof IRLiteralLatLongCoordinateExpression) {
            return ["LiteralLatLongCoordinateExpression", IRLiteralLatLongCoordinateExpression.jsonEmit_IRLiteralLatLongCoordinateExpression(expr)];
        }
        else if(expr instanceof IRLiteralComplexExpression) {
            return ["LiteralComplexExpression", IRLiteralComplexExpression.jsonEmit_IRLiteralComplexExpression(expr)];
        }
        else if(expr instanceof IRLiteralByteBufferExpression) {
            return ["LiteralByteBufferExpression", IRLiteralByteBufferExpression.jsonEmit_IRLiteralByteBufferExpression(expr)];
        }
        else if(expr instanceof IRLiteralUUIDv4Expression) {
            return ["LiteralUUIDv4Expression", IRLiteralUUIDv4Expression.jsonEmit_IRLiteralUUIDv4Expression(expr)];
        }
        else if(expr instanceof IRLiteralUUIDv7Expression) {
            return ["LiteralUUIDv7Expression", IRLiteralUUIDv7Expression.jsonEmit_IRLiteralUUIDv7Expression(expr)];
        }
        else if(expr instanceof IRLiteralSHAContentHashExpression) {
            return ["LiteralSHAContentHashExpression", IRLiteralSHAContentHashExpression.jsonEmit_IRLiteralSHAContentHashExpression(expr)];
        }
        else if(expr instanceof IRLiteralTZDateTimeExpression) {
            return ["LiteralTZDateTimeExpression", IRLiteralTZDateTimeExpression.jsonEmit_IRLiteralTZDateTimeExpression(expr)];
        }
        else if(expr instanceof IRLiteralTAITimeExpression) {
            return ["LiteralTAITimeExpression", IRLiteralTAITimeExpression.jsonEmit_IRLiteralTAITimeExpression(expr)];
        }
        else if(expr instanceof IRLiteralPlainDateExpression) {
            return ["LiteralPlainDateExpression", IRLiteralPlainDateExpression.jsonEmit_IRLiteralPlainDateExpression(expr)];
        }
        else if(expr instanceof IRLiteralPlainTimeExpression) {
            return ["LiteralPlainTimeExpression", IRLiteralPlainTimeExpression.jsonEmit_IRLiteralPlainTimeExpression(expr)];
        }
        else if(expr instanceof IRLiteralLogicalTimeExpression) {
            return ["LiteralLogicalTimeExpression", IRLiteralLogicalTimeExpression.jsonEmit_IRLiteralLogicalTimeExpression(expr)];
        }
        else if(expr instanceof IRLiteralISOTimeStampExpression) {
            return ["LiteralISOTimeStampExpression", IRLiteralISOTimeStampExpression.jsonEmit_IRLiteralISOTimeStampExpression(expr)];
        }
        else if(expr instanceof IRLiteralDeltaDateTimeExpression) {
            return ["LiteralDeltaDateTimeExpression", IRLiteralDeltaDateTimeExpression.jsonEmit_IRLiteralDeltaDateTimeExpression(expr)];
        }
        else if(expr instanceof IRLiteralDeltaISOTimeStampExpression) {
            return ["LiteralDeltaISOTimeStampExpression", IRLiteralDeltaISOTimeStampExpression.jsonEmit_IRLiteralDeltaISOTimeStampExpression(expr)];
        }
        else if(expr instanceof IRLiteralDeltaSecondsExpression) {
            return ["LiteralDeltaSecondsExpression", IRLiteralDeltaSecondsExpression.jsonEmit_IRLiteralDeltaSecondsExpression(expr)];
        }
        else if(expr instanceof IRLiteralDeltaLogicalTimeExpression) {
            return ["LiteralDeltaLogicalTimeExpression", IRLiteralDeltaLogicalTimeExpression.jsonEmit_IRLiteralDeltaLogicalTimeExpression(expr)];
        }
        else if(expr instanceof IRLiteralUnicodeRegexExpression) {
            return ["LiteralUnicodeRegexExpression", IRLiteralUnicodeRegexExpression.jsonEmit_IRLiteralUnicodeRegexExpression(expr)];
        }
        else if(expr instanceof IRLiteralCRegexExpression) {
            return ["LiteralCRegexExpression", IRLiteralCRegexExpression.jsonEmit_IRLiteralCRegexExpression(expr)];
        }
        else if(expr instanceof IRLiteralByteExpression) {
            return ["LiteralByteExpression", IRLiteralByteExpression.jsonEmit_IRLiteralByteExpression(expr)];
        }
        else if(expr instanceof IRLiteralCCharExpression) {
            return ["LiteralCCharExpression", IRLiteralCCharExpression.jsonEmit_IRLiteralCCharExpression(expr)];
        }
        else if(expr instanceof IRLiteralUnicodeCharExpression) {
            return ["LiteralUnicodeCharExpression", IRLiteralUnicodeCharExpression.jsonEmit_IRLiteralUnicodeCharExpression(expr)];
        }
        else if(expr instanceof IRLiteralCStringExpression) {
            return ["LiteralCStringExpression", IRLiteralCStringExpression.jsonEmit_IRLiteralCStringExpression(expr)];
        }
        else if(expr instanceof IRLiteralStringExpression) {
            return ["LiteralStringExpression", IRLiteralStringExpression.jsonEmit_IRLiteralStringExpression(expr)];
        }
        else if(expr instanceof IRLiteralFormatStringExpression) {
            return ["LiteralFormatStringExpression", IRLiteralFormatStringExpression.jsonEmit_IRLiteralFormatStringExpression(expr)];
        }
        else if(expr instanceof IRLiteralFormatCStringExpression) {
            return ["LiteralFormatCStringExpression", IRLiteralFormatCStringExpression.jsonEmit_IRLiteralFormatCStringExpression(expr)];
        }
        else if(expr instanceof IRLiteralTypedExpression) {
            return ["LiteralTypedExpression", IRLiteralTypedExpression.jsonEmit_IRLiteralTypedExpression(expr)];
        }
        else if(expr instanceof IRLiteralTypedStringExpression) {
            return ["LiteralTypedStringExpression", IRLiteralTypedStringExpression.jsonEmit_IRLiteralTypedStringExpression(expr)];
        }
        else if(expr instanceof IRLiteralTypedCStringExpression) {
            return ["LiteralTypedCStringExpression", IRLiteralTypedCStringExpression.jsonEmit_IRLiteralTypedCStringExpression(expr)];
        }
        else if(expr instanceof IRAccessEnvHasExpression) {
            return ["AccessEnvHasExpression", IRAccessEnvHasExpression.jsonEmit_IRAccessEnvHasExpression(expr)];
        }
        else if(expr instanceof IRAccessEnvGetExpression) {
            return ["AccessEnvGetExpression", IRAccessEnvGetExpression.jsonEmit_IRAccessEnvGetExpression(expr)];
        }
        else if(expr instanceof IRAccessEnvTryGetExpression) {
            return ["AccessEnvTryGetExpression", IRAccessEnvTryGetExpression.jsonEmit_IRAccessEnvTryGetExpression(expr)];
        }
        else if(expr instanceof IRTaskAccessIDExpression) {
            return ["TaskAccessIDExpression", IRTaskAccessIDExpression.jsonEmit_IRTaskAccessIDExpression(expr)];
        }
        else if(expr instanceof IRTaskAccessParentIDExpression) {
            return ["TaskAccessParentIDExpression", IRTaskAccessParentIDExpression.jsonEmit_IRTaskAccessParentIDExpression(expr)];
        }
        else if(expr instanceof IRAccessConstantExpression) {
            return ["AccessConstantExpression", IRAccessConstantExpression.jsonEmit_IRAccessConstantExpression(expr)];
        }
        else if(expr instanceof IRAccessEnumExpression) {
            return ["AccessEnumExpression", IRAccessEnumExpression.jsonEmit_IRAccessEnumExpression(expr)];
        }
        else if(expr instanceof IRAccessParameterVariableExpression) {
            return ["AccessParameterVariableExpression", IRAccessParameterVariableExpression.jsonEmit_IRAccessParameterVariableExpression(expr)];
        }
        else if(expr instanceof IRAccessLocalVariableExpression) {
            return ["AccessLocalVariableExpression", IRAccessLocalVariableExpression.jsonEmit_IRAccessLocalVariableExpression(expr)];
        }
        else if(expr instanceof IRAccessCapturedVariableExpression) {
            return ["AccessCapturedVariableExpression", IRAccessCapturedVariableExpression.jsonEmit_IRAccessCapturedVariableExpression(expr)];
        }
        else if(expr instanceof IRAccessTempVariableExpression) {
            return ["AccessTempVariableExpression", IRAccessTempVariableExpression.jsonEmit_IRAccessTempVariableExpression(expr)];
        }
        else if(expr instanceof IRAccessTypeDeclValueExpression) {
            return ["AccessTypeDeclValueExpression", IRAccessTypeDeclValueExpression.jsonEmit_IRAccessTypeDeclValueExpression(expr)];
        }
        else if(expr instanceof IRConstructSafeTypeDeclExpression) {
            return ["ConstructSafeTypeDeclExpression", IRConstructSafeTypeDeclExpression.jsonEmit_IRConstructSafeTypeDeclExpression(expr)];
        }
        else if(expr instanceof IRConstructorSomeTypeExpression) {
            return ["ConstructorSomeTypeExpression", IRConstructorSomeTypeExpression.jsonEmit_IRConstructorSomeTypeExpression(expr)];
        }
        else if(expr instanceof IRConstructorOkTypeExpression) {
            return ["ConstructorOkTypeExpression", IRConstructorOkTypeExpression.jsonEmit_IRConstructorOkTypeExpression(expr)];
        }
        else if(expr instanceof IRConstructorFailTypeExpression) {
            return ["ConstructorFailTypeExpression", IRConstructorFailTypeExpression.jsonEmit_IRConstructorFailTypeExpression(expr)];
        }
        else if(expr instanceof IRConstructorAPISuccessTypeExpression) {
            return ["ConstructorAPISuccessTypeExpression", IRConstructorAPISuccessTypeExpression.jsonEmit_IRConstructorAPISuccessTypeExpression(expr)];
        }
        else if(expr instanceof IRConstructorMapEntryTypeExpression) {
            return ["ConstructorMapEntryTypeExpression", IRConstructorMapEntryTypeExpression.jsonEmit_IRConstructorMapEntryTypeExpression(expr)];
        }
        else if(expr instanceof IRConstructorStandardEntityExpression) {
            return ["ConstructorStandardEntityExpression", IRConstructorStandardEntityExpression.jsonEmit_IRConstructorStandardEntityExpression(expr)];
        }
        else if(expr instanceof IRConstructorLambdaExpression) {
            return ["ConstructorLambdaExpression", IRConstructorLambdaExpression.jsonEmit_IRConstructorLambdaExpression(expr)];
        }
        else if(expr instanceof IRConstructorEListExpression) {
            return ["ConstructorEListExpression", IRConstructorEListExpression.jsonEmit_IRConstructorEListExpression(expr)];
        }
        else if(expr instanceof IRConstructorListEmptyExpression) {
            return ["ConstructorListEmptyExpression", IRConstructorListEmptyExpression.jsonEmit_IRConstructorListEmptyExpression(expr)];
        }
        else if(expr instanceof IRConstructorListPassthroughExpression) {
            return ["ConstructorListPassthroughExpression", IRConstructorListPassthroughExpression.jsonEmit_IRConstructorListPassthroughExpression(expr)];
        }
        else if(expr instanceof IRConstructorListSingletonsExpression) {
            return ["ConstructorListSingletonsExpression", IRConstructorListSingletonsExpression.jsonEmit_IRConstructorListSingletonsExpression(expr)];
        }
        else if(expr instanceof IRConstructorListMixedExpression) {
            return ["ConstructorListMixedExpression", IRConstructorListMixedExpression.jsonEmit_IRConstructorListMixedExpression(expr)];
        }
        else if(expr instanceof IRConstructorMapEmptyExpression) {
            return ["ConstructorMapEmptyExpression", IRConstructorMapEmptyExpression.jsonEmit_IRConstructorMapEmptyExpression(expr)];
        }
        else if(expr instanceof IRConstructorMapSingletonsExpression) {
            return ["ConstructorMapSingletonsExpression", IRConstructorMapSingletonsExpression.jsonEmit_IRConstructorMapSingletonsExpression(expr)];
        }
        else if(expr instanceof IRAccessFieldSpecialExpression) {
            return ["AccessFieldSpecialExpression", IRAccessFieldSpecialExpression.jsonEmit_IRAccessFieldSpecialExpression(expr)];
        }
        else if(expr instanceof IRAccessFieldDirectExpression) {
            return ["AccessFieldDirectExpression", IRAccessFieldDirectExpression.jsonEmit_IRAccessFieldDirectExpression(expr)];
        }
        else if(expr instanceof IRAccessFieldVirtualExpression) {
            return ["AccessFieldVirtualExpression", IRAccessFieldVirtualExpression.jsonEmit_IRAccessFieldVirtualExpression(expr)];
        }
        else if(expr instanceof IRAccessEListIndexExpression) {
            return ["AccessEListIndexExpression", IRAccessEListIndexExpression.jsonEmit_IRAccessEListIndexExpression(expr)];
        }
        else if(expr instanceof IRInvokeSimpleExpression) {
            return ["InvokeSimpleExpression", IRInvokeSimpleExpression.jsonEmit_IRInvokeSimpleExpression(expr)];
        }
        else if(expr instanceof IRInvokeSimpleWithImplicitsExpression) {
            return ["InvokeSimpleWithImplicitsExpression", IRInvokeSimpleWithImplicitsExpression.jsonEmit_IRInvokeSimpleWithImplicitsExpression(expr)];
        }
        else if(expr instanceof IRInvokeVirtualSimpleExpression) {
            return ["InvokeVirtualSimpleExpression", IRInvokeVirtualSimpleExpression.jsonEmit_IRInvokeVirtualSimpleExpression(expr)];
        }
        else if(expr instanceof IRInvokeVirtualWithImplicitsExpression) {
            return ["InvokeVirtualWithImplicitsExpression", IRInvokeVirtualWithImplicitsExpression.jsonEmit_IRInvokeVirtualWithImplicitsExpression(expr)];
        }
        else if(expr instanceof IRInvokeCallAgentOrAPIExpression) {
            return ["InvokeCallAgentOrAPIExpression", IRInvokeCallAgentOrAPIExpression.jsonEmit_IRInvokeCallAgentOrAPIExpression(expr)];
        }
        else if(expr instanceof IRInvokeTaskActionExpression) {
            return ["InvokeTaskActionExpression", IRInvokeTaskActionExpression.jsonEmit_IRInvokeTaskActionExpression(expr)];
        }
        else if(expr instanceof IRInterpolateFormatCStringExpression) {
            return ["InterpolateFormatCStringExpression", IRInterpolateFormatCStringExpression.jsonEmit_IRInterpolateFormatCStringExpression(expr)];
        }
        else if(expr instanceof IRInterpolateFormatStringExpression) {
            return ["InterpolateFormatStringExpression", IRInterpolateFormatStringExpression.jsonEmit_IRInterpolateFormatStringExpression(expr)];
        }
        else if(expr instanceof IRPrefixNotOpExpression) {
            return ["PrefixNotOpExpression", IRPrefixNotOpExpression.jsonEmit_IRPrefixNotOpExpression(expr)];
        }
        else if(expr instanceof IRPrefixNegateOpExpression) {
            return ["PrefixNegateOpExpression", IRPrefixNegateOpExpression.jsonEmit_IRPrefixNegateOpExpression(expr)];
        }
        else if(expr instanceof IRPrefixPlusOpExpression) {
            return ["PrefixPlusOpExpression", IRPrefixPlusOpExpression.jsonEmit_IRPrefixPlusOpExpression(expr)];
        }
        else if(expr instanceof IRBinAddExpression) {
            return ["BinAddExpression", IRBinAddExpression.jsonEmit_IRBinAddExpression(expr)];
        }
        else if(expr instanceof IRBinSubExpression) {
            return ["BinSubExpression", IRBinSubExpression.jsonEmit_IRBinSubExpression(expr)];
        }
        else if(expr instanceof IRBinMultExpression) {
            return ["BinMultExpression", IRBinMultExpression.jsonEmit_IRBinMultExpression(expr)];
        }
        else if(expr instanceof IRBinDivExpression) {
            return ["BinDivExpression", IRBinDivExpression.jsonEmit_IRBinDivExpression(expr)];
        }
        else if(expr instanceof IRNumericEqExpression) {
            return ["NumericEqExpression", IRNumericEqExpression.jsonEmit_IRNumericEqExpression(expr)];
        }
        else if(expr instanceof IRNumericNeqExpression) {
            return ["NumericNeqExpression", IRNumericNeqExpression.jsonEmit_IRNumericNeqExpression(expr)];
        }
        else if(expr instanceof IRNumericLessExpression) {
            return ["NumericLessExpression", IRNumericLessExpression.jsonEmit_IRNumericLessExpression(expr)];
        }
        else if(expr instanceof IRNumericLessEqExpression) {
            return ["NumericLessEqExpression", IRNumericLessEqExpression.jsonEmit_IRNumericLessEqExpression(expr)];
        }
        else if(expr instanceof IRNumericGreaterExpression) {
            return ["NumericGreaterExpression", IRNumericGreaterExpression.jsonEmit_IRNumericGreaterExpression(expr)];
        }
        else if(expr instanceof IRNumericGreaterEqExpression) {
            return ["NumericGreaterEqExpression", IRNumericGreaterEqExpression.jsonEmit_IRNumericGreaterEqExpression(expr)];
        }
        else if(expr instanceof IRIsNoneOptionExpression) {
            return ["IsNoneOptionExpression", IRIsNoneOptionExpression.jsonEmit_IRIsNoneOptionExpression(expr)];
        }
        else if(expr instanceof IRIsNotNoneOptionExpression) {
            return ["IsNotNoneOptionExpression", IRIsNotNoneOptionExpression.jsonEmit_IRIsNotNoneOptionExpression(expr)];
        }
        else if(expr instanceof IRIsOptionEqValueExpression) {
            return ["IsOptionEqValueExpression", IRIsOptionEqValueExpression.jsonEmit_IRIsOptionEqValueExpression(expr)];
        }
        else if(expr instanceof IRIsOptionNeqValueExpression) {
            return ["IsOptionNeqValueExpression", IRIsOptionNeqValueExpression.jsonEmit_IRIsOptionNeqValueExpression(expr)];
        }
        else if(expr instanceof IRIsSomeEqValueExpression) {
            return ["IsSomeEqValueExpression", IRIsSomeEqValueExpression.jsonEmit_IRIsSomeEqValueExpression(expr)];
        }
        else if(expr instanceof IRIsSomeNeqValueExpression) {
            return ["IsSomeNeqValueExpression", IRIsSomeNeqValueExpression.jsonEmit_IRIsSomeNeqValueExpression(expr)];
        }
        else if(expr instanceof IRBinKeyEqDirectExpression) {
            return ["BinKeyEqDirectExpression", IRBinKeyEqDirectExpression.jsonEmit_IRBinKeyEqDirectExpression(expr)];
        }
        else if(expr instanceof IRBinKeyNeqDirectExpression) {
            return ["BinKeyNeqDirectExpression", IRBinKeyNeqDirectExpression.jsonEmit_IRBinKeyNeqDirectExpression(expr)];
        }
        else if(expr instanceof IRBinKeyLessDirectExpression) {
            return ["BinKeyLessDirectExpression", IRBinKeyLessDirectExpression.jsonEmit_IRBinKeyLessDirectExpression(expr)];
        }
        else if(expr instanceof IRLogicAndExpression) {
            return ["LogicAndExpression", IRLogicAndExpression.jsonEmit_IRLogicAndExpression(expr)];
        }
        else if(expr instanceof IRLogicOrExpression) {
            return ["LogicOrExpression", IRLogicOrExpression.jsonEmit_IRLogicOrExpression(expr)];
        }
        else if(expr instanceof IRLogicSimpleConditionalExpression) {
            return ["LogicSimpleConditionalExpression", IRLogicSimpleConditionalExpression.jsonEmit_IRLogicSimpleConditionalExpression(expr)];
        }
        else if(expr instanceof IRLiteralOptionOfNoneExpression) {
            return ["LiteralOptionOfNoneExpression", IRLiteralOptionOfNoneExpression.jsonEmit_IRLiteralOptionOfNoneExpression(expr)];
        }
        else if(expr instanceof IRConstructOptionFromSomeExpression) {
            return ["ConstructOptionFromSomeExpression", IRConstructOptionFromSomeExpression.jsonEmit_IRConstructOptionFromSomeExpression(expr)];
        }
        else if(expr instanceof IRExtractSomeFromOptionExpression) {
            return ["ExtractSomeFromOptionExpression", IRExtractSomeFromOptionExpression.jsonEmit_IRExtractSomeFromOptionExpression(expr)];
        }
        else if(expr instanceof IRExtractSomeValueFromOptionExpression) {
            return ["ExtractSomeValueFromOptionExpression", IRExtractSomeValueFromOptionExpression.jsonEmit_IRExtractSomeValueFromOptionExpression(expr)];
        }
        else if(expr instanceof IRConstructResultFromOkExpression) {
            return ["ConstructResultFromOkExpression", IRConstructResultFromOkExpression.jsonEmit_IRConstructResultFromOkExpression(expr)];
        }
        else if(expr instanceof IRConstructResultFromFailExpression) {
            return ["ConstructResultFromFailExpression", IRConstructResultFromFailExpression.jsonEmit_IRConstructResultFromFailExpression(expr)];
        }
        else if(expr instanceof IRExtractOkFromResultExpression) {
            return ["ExtractOkFromResultExpression", IRExtractOkFromResultExpression.jsonEmit_IRExtractOkFromResultExpression(expr)];
        }
        else if(expr instanceof IRExtractOkValueFromResultExpression) {
            return ["ExtractOkValueFromResultExpression", IRExtractOkValueFromResultExpression.jsonEmit_IRExtractOkValueFromResultExpression(expr)];
        }
        else if(expr instanceof IRExtractFailFromResultExpression) {
            return ["ExtractFailFromResultExpression", IRExtractFailFromResultExpression.jsonEmit_IRExtractFailFromResultExpression(expr)];
        }
        else if(expr instanceof IRExtractFailValueFromResultExpression) {
            return ["ExtractFailValueFromResultExpression", IRExtractFailValueFromResultExpression.jsonEmit_IRExtractFailValueFromResultExpression(expr)];
        }
        else if(expr instanceof IRIsConceptRepresentationOfTypeExpression) {
            return ["IsConceptRepresentationOfTypeExpression", IRIsConceptRepresentationOfTypeExpression.jsonEmit_IRIsConceptRepresentationOfTypeExpression(expr)];
        }
        else if(expr instanceof IRIsNotConceptRepresentationOfTypeExpression) {
            return ["IsNotConceptRepresentationOfTypeExpression", IRIsNotConceptRepresentationOfTypeExpression.jsonEmit_IRIsNotConceptRepresentationOfTypeExpression(expr)];
        }
        else if(expr instanceof IRIsConceptRepresentationSubtypeOfTypeExpression) {
            return ["IsConceptRepresentationSubtypeOfTypeExpression", IRIsConceptRepresentationSubtypeOfTypeExpression.jsonEmit_IRIsConceptRepresentationSubtypeOfTypeExpression(expr)];
        }
        else if(expr instanceof IRIsNotConceptRepresentationSubtypeOfTypeExpression) {
            return ["IsNotConceptRepresentationSubtypeOfTypeExpression", IRIsNotConceptRepresentationSubtypeOfTypeExpression.jsonEmit_IRIsNotConceptRepresentationSubtypeOfTypeExpression(expr)];
        }
        else if(expr instanceof IRStaticIsTypeSubtypeOfExpression) {
            return ["StaticIsTypeSubtypeOfExpression", IRStaticIsTypeSubtypeOfExpression.jsonEmit_IRStaticIsTypeSubtypeOfExpression(expr)];
        }
        else if(expr instanceof IRBoxEntityToConceptRepresentationExpression) {
            return ["BoxEntityToConceptRepresentationExpression", IRBoxEntityToConceptRepresentationExpression.jsonEmit_IRBoxEntityToConceptRepresentationExpression(expr)];
        }
        else if(expr instanceof IRUnboxEntityFromConceptRepresentationExpression) {
            return ["UnboxEntityFromConceptRepresentationExpression", IRUnboxEntityFromConceptRepresentationExpression.jsonEmit_IRUnboxEntityFromConceptRepresentationExpression(expr)];
        }
        else if(expr instanceof IRConvertConceptRepresentationExpression) {
            return ["ConvertConceptRepresentationExpression", IRConvertConceptRepresentationExpression.jsonEmit_IRConvertConceptRepresentationExpression(expr)];
        }
        else {
            assert(false, `Unknown IRExpression kind: ${expr.tag}`);
        }
    }

    static jsonParse_IRExpression(obj: any): IRExpression {
        const kind = obj[0];
        const value = obj[1];

        switch(kind) {
            case "LiteralNoneExpression": {
                return IRLiteralNoneExpression.jsonParse_IRLiteralNoneExpression(value);
            }
            case "LiteralBoolExpression": {
                return IRLiteralBoolExpression.jsonParse_IRLiteralBoolExpression(value);
            }
            case "LiteralNatExpression": {
                return IRLiteralNatExpression.jsonParse_IRLiteralNatExpression(value);
            }
            case "LiteralIntExpression": {
                return IRLiteralIntExpression.jsonParse_IRLiteralIntExpression(value);
            }
            case "LiteralChkNatExpression": {
                return IRLiteralChkNatExpression.jsonParse_IRLiteralChkNatExpression(value);
            }
            case "LiteralChkIntExpression": {
                return IRLiteralChkIntExpression.jsonParse_IRLiteralChkIntExpression(value);
            }
            case "LiteralRationalExpression": {
                return IRLiteralRationalExpression.jsonParse_IRLiteralRationalExpression(value);
            }
            case "LiteralFloatExpression": {
                return IRLiteralFloatExpression.jsonParse_IRLiteralFloatExpression(value);
            }
            case "LiteralDecimalExpression": {
                return IRLiteralDecimalExpression.jsonParse_IRLiteralDecimalExpression(value);
            }
            case "LiteralDecimalDegreeExpression": {
                return IRLiteralDecimalDegreeExpression.jsonParse_IRLiteralDecimalDegreeExpression(value);
            }
            case "LiteralLatLongCoordinateExpression": {
                return IRLiteralLatLongCoordinateExpression.jsonParse_IRLiteralLatLongCoordinateExpression(value);
            }
            case "LiteralComplexExpression": {
                return IRLiteralComplexExpression.jsonParse_IRLiteralComplexExpression(value);
            }
            case "LiteralByteBufferExpression": {
                return IRLiteralByteBufferExpression.jsonParse_IRLiteralByteBufferExpression(value);
            }
            case "LiteralUUIDv4Expression": {
                return IRLiteralUUIDv4Expression.jsonParse_IRLiteralUUIDv4Expression(value);
            }
            case "LiteralUUIDv7Expression": {
                return IRLiteralUUIDv7Expression.jsonParse_IRLiteralUUIDv7Expression(value);
            }
            case "LiteralSHAContentHashExpression": {
                return IRLiteralSHAContentHashExpression.jsonParse_IRLiteralSHAContentHashExpression(value);
            }
            case "LiteralTZDateTimeExpression": {
                return IRLiteralTZDateTimeExpression.jsonParse_IRLiteralTZDateTimeExpression(value);
            }
            case "LiteralTAITimeExpression": {
                return IRLiteralTAITimeExpression.jsonParse_IRLiteralTAITimeExpression(value);
            }
            case "LiteralPlainDateExpression": {
                return IRLiteralPlainDateExpression.jsonParse_IRLiteralPlainDateExpression(value);
            }
            case "LiteralPlainTimeExpression": {
                return IRLiteralPlainTimeExpression.jsonParse_IRLiteralPlainTimeExpression(value);
            }
            case "LiteralLogicalTimeExpression": {
                return IRLiteralLogicalTimeExpression.jsonParse_IRLiteralLogicalTimeExpression(value);
            }
            case "LiteralISOTimeStampExpression": {
                return IRLiteralISOTimeStampExpression.jsonParse_IRLiteralISOTimeStampExpression(value);
            }
            case "LiteralDeltaDateTimeExpression": {
                return IRLiteralDeltaDateTimeExpression.jsonParse_IRLiteralDeltaDateTimeExpression(value);
            }
            case "LiteralDeltaISOTimeStampExpression": {
                return IRLiteralDeltaISOTimeStampExpression.jsonParse_IRLiteralDeltaISOTimeStampExpression(value);
            }
            case "LiteralDeltaSecondsExpression": {
                return IRLiteralDeltaSecondsExpression.jsonParse_IRLiteralDeltaSecondsExpression(value);
            }
            case "LiteralDeltaLogicalTimeExpression": {
                return IRLiteralDeltaLogicalTimeExpression.jsonParse_IRLiteralDeltaLogicalTimeExpression(value);
            }
            case "LiteralUnicodeRegexExpression": {
                return IRLiteralUnicodeRegexExpression.jsonParse_IRLiteralUnicodeRegexExpression(value);
            }
            case "LiteralCRegexExpression": {
                return IRLiteralCRegexExpression.jsonParse_IRLiteralCRegexExpression(value);
            }
            case "LiteralByteExpression": {
                return IRLiteralByteExpression.jsonParse_IRLiteralByteExpression(value);
            }
            case "LiteralCCharExpression": {
                return IRLiteralCCharExpression.jsonParse_IRLiteralCCharExpression(value);
            }
            case "LiteralUnicodeCharExpression": {
                return IRLiteralUnicodeCharExpression.jsonParse_IRLiteralUnicodeCharExpression(value);
            }
            case "LiteralCStringExpression": {
                return IRLiteralCStringExpression.jsonParse_IRLiteralCStringExpression(value);
            }
            case "LiteralStringExpression": {
                return IRLiteralStringExpression.jsonParse_IRLiteralStringExpression(value);
            }
            case "LiteralFormatStringExpression": {
                return IRLiteralFormatStringExpression.jsonParse_IRLiteralFormatStringExpression(value);
            }
            case "LiteralFormatCStringExpression": {
                return IRLiteralFormatCStringExpression.jsonParse_IRLiteralFormatCStringExpression(value);
            }
            case "LiteralTypedExpression": {
                return IRLiteralTypedExpression.jsonParse_IRLiteralTypedExpression(value);
            }
            case "LiteralTypedStringExpression": {
                return IRLiteralTypedStringExpression.jsonParse_IRLiteralTypedStringExpression(value);
            }
            case "LiteralTypedCStringExpression": {
                return IRLiteralTypedCStringExpression.jsonParse_IRLiteralTypedCStringExpression(value);
            }
            case "AccessEnvHasExpression": {
                return IRAccessEnvHasExpression.jsonParse_IRAccessEnvHasExpression(value);
            }
            case "AccessEnvGetExpression": {
                return IRAccessEnvGetExpression.jsonParse_IRAccessEnvGetExpression(value);
            }
            case "AccessEnvTryGetExpression": {
                return IRAccessEnvTryGetExpression.jsonParse_IRAccessEnvTryGetExpression(value);
            }
            case "TaskAccessIDExpression": {
                return IRTaskAccessIDExpression.jsonParse_IRTaskAccessIDExpression(value);
            }
            case "TaskAccessParentIDExpression": {
                return IRTaskAccessParentIDExpression.jsonParse_IRTaskAccessParentIDExpression(value);
            }
            case "AccessConstantExpression": {
                return IRAccessConstantExpression.jsonParse_IRAccessConstantExpression(value);
            }
            case "AccessEnumExpression": {
                return IRAccessEnumExpression.jsonParse_IRAccessEnumExpression(value);
            }
            case "AccessParameterVariableExpression": {
                return IRAccessParameterVariableExpression.jsonParse_IRAccessParameterVariableExpression(value);
            }
            case "AccessLocalVariableExpression": {
                return IRAccessLocalVariableExpression.jsonParse_IRAccessLocalVariableExpression(value);
            }
            case "AccessCapturedVariableExpression": {
                return IRAccessCapturedVariableExpression.jsonParse_IRAccessCapturedVariableExpression(value);
            }
            case "AccessTempVariableExpression": {
                return IRAccessTempVariableExpression.jsonParse_IRAccessTempVariableExpression(value);
            }
            case "AccessTypeDeclValueExpression": {
                return IRAccessTypeDeclValueExpression.jsonParse_IRAccessTypeDeclValueExpression(value);
            }
            case "ConstructSafeTypeDeclExpression": {
                return IRConstructSafeTypeDeclExpression.jsonParse_IRConstructSafeTypeDeclExpression(value);
            }
            case "ConstructSomeTypeExpression": {
                return IRConstructorSomeTypeExpression.jsonParse_IRConstructorSomeTypeExpression(value);
            }
            case "ConstructOkTypeExpression": {
                return IRConstructorOkTypeExpression.jsonParse_IRConstructorOkTypeExpression(value);
            }
            case "ConstructFailTypeExpression": {
                return IRConstructorFailTypeExpression.jsonParse_IRConstructorFailTypeExpression(value);
            }
            case "ConstructAPISuccessTypeExpression": {
                return IRConstructorAPISuccessTypeExpression.jsonParse_IRConstructorAPISuccessTypeExpression(value);
            }
            case "ConstructMapEntryTypeExpression": {
                return IRConstructorMapEntryTypeExpression.jsonParse_IRConstructorMapEntryTypeExpression(value);
            }
            case "ConstructStandardEntityExpression": {
                return IRConstructorStandardEntityExpression.jsonParse_IRConstructorStandardEntityExpression(value);
            }
            case "ConstructLambdaExpression": {
                return IRConstructorLambdaExpression.jsonParse_IRConstructorLambdaExpression(value);
            }
            case "ConstructEListExpression": {
                return IRConstructorEListExpression.jsonParse_IRConstructorEListExpression(value);
            }
            case "ConstructListEmptyExpression": {
                return IRConstructorListEmptyExpression.jsonParse_IRConstructorListEmptyExpression(value);
            }
            case "ConstructListPassthroughExpression": {
                return IRConstructorListPassthroughExpression.jsonParse_IRConstructorListPassthroughExpression(value);
            }
            case "ConstructListSingletonsExpression": {
                return IRConstructorListSingletonsExpression.jsonParse_IRConstructorListSingletonsExpression(value);
            }
            case "ConstructListMixedExpression": {
                return IRConstructorListMixedExpression.jsonParse_IRConstructorListMixedExpression(value);
            }
            case "ConstructMapEmptyExpression": {
                return IRConstructorMapEmptyExpression.jsonParse_IRConstructorMapEmptyExpression(value);
            }
            case "ConstructMapSingletonsExpression": {
                return IRConstructorMapSingletonsExpression.jsonParse_IRConstructorMapSingletonsExpression(value);
            }
            case "AccessFieldSpecialExpression": {
                return IRAccessFieldSpecialExpression.jsonParse_IRAccessFieldSpecialExpression(value);
            }
            case "AccessFieldDirectExpression": {
                return IRAccessFieldDirectExpression.jsonParse_IRAccessFieldDirectExpression(value);
            }
            case "AccessFieldVirtualExpression": {
                return IRAccessFieldVirtualExpression.jsonParse_IRAccessFieldVirtualExpression(value);
            }
            case "AccessEListIndexExpression": {
                return IRAccessEListIndexExpression.jsonParse_IRAccessEListIndexExpression(value);
            }
            case "InvokeSimpleExpression": {
                return IRInvokeSimpleExpression.jsonParse_IRInvokeSimpleExpression(value);
            }
            case "InvokeSimpleWithImplicitsExpression": {
                return IRInvokeSimpleWithImplicitsExpression.jsonParse_IRInvokeSimpleWithImplicitsExpression(value);
            }
            case "InvokeVirtualSimpleExpression": {
                return IRInvokeVirtualSimpleExpression.jsonParse_IRInvokeVirtualSimpleExpression(value);
            }
            case "InvokeVirtualWithImplicitsExpression": {
                return IRInvokeVirtualWithImplicitsExpression.jsonParse_IRInvokeVirtualWithImplicitsExpression(value);
            }
            case "InvokeCallAgentOrAPIExpression": {
                return IRInvokeCallAgentOrAPIExpression.jsonParse_IRInvokeCallAgentOrAPIExpression(value);
            }
            case "InvokeTaskActionExpression": {
                return IRInvokeTaskActionExpression.jsonParse_IRInvokeTaskActionExpression(value);
            }
            case "InterpolateFormatCStringExpression": {
                return IRInterpolateFormatCStringExpression.jsonParse_IRInterpolateFormatCStringExpression(value);
            }
            case "InterpolateFormatStringExpression": {
                return IRInterpolateFormatStringExpression.jsonParse_IRInterpolateFormatStringExpression(value);
            }
            case "PrefixNotOpExpression": {
                return IRPrefixNotOpExpression.jsonParse_IRPrefixNotOpExpression(value);
            }
            case "PrefixNegateOpExpression": {
                return IRPrefixNegateOpExpression.jsonParse_IRPrefixNegateOpExpression(value);
            }
            case "PrefixPlusOpExpression": {
                return IRPrefixPlusOpExpression.jsonParse_IRPrefixPlusOpExpression(value);
            }
            case "BinAddExpression": {
                return IRBinAddExpression.jsonParse_IRBinAddExpression(value);
            }
            case "BinSubExpression": {
                return IRBinSubExpression.jsonParse_IRBinSubExpression(value);
            }
            case "BinMultExpression": {
                return IRBinMultExpression.jsonParse_IRBinMultExpression(value);
            }
            case "BinDivExpression": {
                return IRBinDivExpression.jsonParse_IRBinDivExpression(value);
            }
            case "NumericEqExpression": {
                return IRNumericEqExpression.jsonParse_IRNumericEqExpression(value);
            }
            case "NumericNeqExpression": {
                return IRNumericNeqExpression.jsonParse_IRNumericNeqExpression(value);
            }
            case "NumericLessExpression": {
                return IRNumericLessExpression.jsonParse_IRNumericLessExpression(value);
            }
            case "NumericLessEqExpression": {
                return IRNumericLessEqExpression.jsonParse_IRNumericLessEqExpression(value);
            }
            case "NumericGreaterExpression": {
                return IRNumericGreaterExpression.jsonParse_IRNumericGreaterExpression(value);
            }
            case "NumericGreaterEqExpression": {
                return IRNumericGreaterEqExpression.jsonParse_IRNumericGreaterEqExpression(value);
            }
            case "IsNoneOptionExpression": {
                return IRIsNoneOptionExpression.jsonParse_IRIsNoneOptionExpression(value);
            }
            case "IsNotNoneOptionExpression": {
                return IRIsNotNoneOptionExpression.jsonParse_IRIsNotNoneOptionExpression(value);
            }
            case "IsOptionEqValueExpression": {
                return IRIsOptionEqValueExpression.jsonParse_IRIsOptionEqValueExpression(value);
            }
            case "IsOptionNeqValueExpression": {
                return IRIsOptionNeqValueExpression.jsonParse_IRIsOptionNeqValueExpression(value);
            }
            case "IsSomeEqValueExpression": {
                return IRIsSomeEqValueExpression.jsonParse_IRIsSomeEqValueExpression(value);
            }
            case "IsSomeNeqValueExpression": {
                return IRIsSomeNeqValueExpression.jsonParse_IRIsSomeNeqValueExpression(value);
            }
            case "LogicAndExpression": {
                return IRLogicAndExpression.jsonParse_IRLogicAndExpression(value);
            }
            case "LogicOrExpression": {
                return IRLogicOrExpression.jsonParse_IRLogicOrExpression(value);
            }
            case "LogicSimpleConditionalExpression": {
                return IRLogicSimpleConditionalExpression.jsonParse_IRLogicSimpleConditionalExpression(value);
            }
            case "LiteralOptionOfNoneExpression": {
                return IRLiteralOptionOfNoneExpression.jsonParse_IRLiteralOptionOfNoneExpression(value);
            }
            case "ConstructOptionFromSomeExpression": {
                return IRConstructOptionFromSomeExpression.jsonParse_IRConstructOptionFromSomeExpression(value);
            }
            case "ExtractSomeFromOptionExpression": {
                return IRExtractSomeFromOptionExpression.jsonParse_IRExtractSomeFromOptionExpression(value);
            }
            case "ExtractSomeValueFromOptionExpression": {
                return IRExtractSomeValueFromOptionExpression.jsonParse_IRExtractSomeValueFromOptionExpression(value);
            }
            case "ConstructResultFromOkExpression": {
                return IRConstructResultFromOkExpression.jsonParse_IRConstructResultFromOkExpression(value);
            }
            case "ConstructResultFromFailExpression": {
                return IRConstructResultFromFailExpression.jsonParse_IRConstructResultFromFailExpression(value);
            }
            case "ExtractOkFromResultExpression": {
                return IRExtractOkFromResultExpression.jsonParse_IRExtractOkFromResultExpression(value);
            }
            case "ExtractOkValueFromResultExpression": {
                return IRExtractOkValueFromResultExpression.jsonParse_IRExtractOkValueFromResultExpression(value);
            }
            case "ExtractFailFromResultExpression": {
                return IRExtractFailFromResultExpression.jsonParse_IRExtractFailFromResultExpression(value);
            }
            case "ExtractFailValueFromResultExpression": {
                return IRExtractFailValueFromResultExpression.jsonParse_IRExtractFailValueFromResultExpression(value);
            }
            case "IsConceptRepresentationOfTypeExpression": {
                return IRIsConceptRepresentationOfTypeExpression.jsonParse_IRIsConceptRepresentationOfTypeExpression(value);
            }
            case "IsNotConceptRepresentationOfTypeExpression": {
                return IRIsNotConceptRepresentationOfTypeExpression.jsonParse_IRIsNotConceptRepresentationOfTypeExpression(value);
            }
            case "IsConceptRepresentationSubtypeOfTypeExpression": {
                return IRIsConceptRepresentationSubtypeOfTypeExpression.jsonParse_IRIsConceptRepresentationSubtypeOfTypeExpression(value);
            }
            case "IsNotConceptRepresentationSubtypeOfTypeExpression": {
                return IRIsNotConceptRepresentationSubtypeOfTypeExpression.jsonParse_IRIsNotConceptRepresentationSubtypeOfTypeExpression(value);
            }
            case "StaticIsTypeSubtypeOfExpression": {
                return IRStaticIsTypeSubtypeOfExpression.jsonParse_IRStaticIsTypeSubtypeOfExpression(value);
            }
            case "BoxEntityToConceptRepresentationExpression": {
                return IRBoxEntityToConceptRepresentationExpression.jsonParse_IRBoxEntityToConceptRepresentationExpression(value);
            }
            case "UnboxEntityFromConceptRepresentationExpression": {
                return IRUnboxEntityFromConceptRepresentationExpression.jsonParse_IRUnboxEntityFromConceptRepresentationExpression(value);
            }
            case "ConvertConceptRepresentationExpression": {
                return IRConvertConceptRepresentationExpression.jsonParse_IRConvertConceptRepresentationExpression(value);
            }
            default: {
                assert(false, `Unknown IR expression kind: ${kind}`);
            }
        }
    }
}

/* This class represents expressions that are invocations (function/method/virtual calls) */
abstract class IRInvokeExpression extends IRExpression {
    readonly ikey: string;
    readonly args: IRSimpleExpression[];

    constructor(tag: IRExpressionTag, ikey: string, args: IRSimpleExpression[]) {
        super(tag);
        this.ikey = ikey;
        this.args = args;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    static jsonEmit_IRInvokeExpression(expr: IRInvokeExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(expr);
    }

    static jsonParse_IRInvokeExpression(obj: any): IRInvokeExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRInvokeExpression;
    }
}

/* This class represents expressions that have a single return value */
abstract class IRInvokeDirectExpression extends IRInvokeExpression {
    constructor(tag: IRExpressionTag, ikey: string, args: IRSimpleExpression[]) {
        super(tag, ikey, args);
    }

    static jsonEmit_IRInvokeDirectExpression(expr: IRInvokeDirectExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(expr);
    }

    static jsonParse_IRInvokeDirectExpression(obj: any): IRInvokeDirectExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRInvokeDirectExpression;
    }
}

enum IRImplicitInvokeArgPassKind {
    Ref = "IRImplicitInvokeArgPassKind#Ref",
    Out = "IRImplicitInvokeArgPassKind#Out",
    OutCond = "IRImplicitInvokeArgPassKind#OutCond",
    InOut = "IRImplicitInvokeArgPassKind#InOut"
}

/* This class represents expressions that have implicit return values */
abstract class IRInvokeImplicitsExpression extends IRInvokeExpression {
    readonly implicitidx: number;
    readonly ivar: string; //the implicit variable to assign the returned ref/out/out?/inout parameter
    readonly ivartype: IRTypeSignature;
    readonly passkind : IRImplicitInvokeArgPassKind;

    constructor(tag: IRExpressionTag, ikey: string, args: IRSimpleExpression[], implicitidx: number, ivar: string, ivartype: IRTypeSignature, passkind: IRImplicitInvokeArgPassKind) {
        super(tag, ikey, args);
        this.implicitidx = implicitidx;
        this.ivar = ivar;
        this.ivartype = ivartype;
        this.passkind = passkind;
    }

    static jsonEmit_IRInvokeImplicitsExpression(expr: IRInvokeImplicitsExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(expr);
    }

    static jsonParse_IRInvokeImplicitsExpression(obj: any): IRInvokeImplicitsExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRInvokeImplicitsExpression;
    }

    static jsonEmitMeta_IRInvokeImplicitsExpression(iie: IRInvokeImplicitsExpression): object {
        return {
            implicitidx: iie.implicitidx,
            ivar: iie.ivar,
            ivartype: IRTypeSignature.jsonEmit_IRTypeSignature(iie.ivartype),
            passkind: `Assembly::${iie.passkind}`
        }
    }

    static jsonParseMeta_IRInvokeImplicitsExpression(obj: any): [number, string, IRTypeSignature, IRImplicitInvokeArgPassKind] {
        return [
            obj.implicitidx,
            obj.ivar,
            IRTypeSignature.jsonParse_IRTypeSignature(obj.ivartype),
            obj.passkind.replace("Assembly::", "") as IRImplicitInvokeArgPassKind
        ];
    }
}

/* This class represents expressions that construct composite (maybe allocating) values -- can only OOM (otherwise semantically safe) but we want to keep them ordered strongly */
abstract class IRConstructExpression extends IRExpression {
    readonly constype: IRNominalTypeSignature;

    constructor(tag: IRExpressionTag, constype: IRNominalTypeSignature) {
        super(tag);
        this.constype = constype;
    }

    override isSimpleExpression(): boolean {
        return true;
    }

    static jsonEmit_IRConstructExpression(expr: IRConstructExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(expr);
    }

    static jsonParse_IRConstructExpression(obj: any): IRConstructExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRConstructExpression;
    }

    static jsonEmitMeta_IRConstructExpression(ce: IRConstructExpression): object {
        return {
            constype: IRNominalTypeSignature.jsonEmit_IRTypeSignature(ce.constype)
        }
    }

    static jsonParseMeta_IRConstructExpression(obj: any): IRNominalTypeSignature {
        return IRNominalTypeSignature.jsonParse_IRTypeSignature(obj.constype) as IRNominalTypeSignature;
    }
}

/* This class represents expressions that are simple and side-effect free (i.e., immediate expressions plus simple operations that we can put into expression trees) */
abstract class IRSimpleExpression extends IRExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }

    override isSimpleExpression(): boolean {
        return true;
    }

    static jsonEmit_IRSimpleExpression(expr: IRSimpleExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(expr);
    }

    static jsonParse_IRSimpleExpression(obj: any): IRSimpleExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRSimpleExpression;
    }
}

/* This class represents expressions that are guaranteed to be immediate values (i.e., vars, literals, constants) */
abstract class IRImmediateExpression extends IRSimpleExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }

    static jsonEmit_IRImmediateExpression(expr: IRImmediateExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(expr);
    }

    static jsonParse_IRImmediateExpression(obj: any): IRImmediateExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRImmediateExpression;
    }
}

/* This class represents expressions that are guaranteed to be immediate values (i.e., constants, typdecl literals) */
abstract class IRLiteralExpression extends IRImmediateExpression {
    constructor(tag: IRExpressionTag) {
        super(tag);
    }

    static jsonEmit_IRLiteralExpression(expr: IRLiteralExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(expr);
    }

    static jsonParse_IRLiteralExpression(obj: any): IRLiteralExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRLiteralExpression;
    }
}

/* This class represents expressions that access field values */
abstract class IRAccessFieldExpression extends IRSimpleExpression {
    readonly eexptype: IRNominalTypeSignature;
    readonly eexp: IRSimpleExpression;
    readonly intype: IRNominalTypeSignature;
    readonly fieldname: string;
    readonly fieldtype: IRTypeSignature;

    constructor(tag: IRExpressionTag, eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature) {
        super(tag);
        this.eexptype = eexptype;
        this.eexp = eexp;
        this.intype = intype;
        this.fieldname = fieldname;
        this.fieldtype = fieldtype;
    }

    static jsonEmit_IRAccessFieldExpression(expr: IRAccessFieldExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(expr);
    }

    static jsonParse_IRAccessFieldExpression(obj: any): IRAccessFieldExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRAccessFieldExpression;
    }
}

enum IRStatementTag {
    IRNopStatement = "IRNopStatement",

    IRTempAssignExpressionStatement = "IRTempAssignExpressionStatement",
    IRTempAssignStdInvokeStatement = "IRTempAssignStdInvokeStatement",
    IRTempAssignRefInvokeStatement = "IRTempAssignRefInvokeStatement",
    IRTempAssignDirectConstructorStatement = "IRTempAssignDirectConstructorStatement",

    IRVariableDeclarationStatement = "IRVariableDeclarationStatement",

    IRVariableInitializationStatement = "IRVariableInitializationStatement",
    IRVariableInitializationDirectInvokeStatement = "IRVariableInitializationDirectInvokeStatement",
    IRVariableInitializationDirectInvokeWithImplicitStatement = "IRVariableInitializationDirectInvokeWithImplicitStatement",
    IRVariableInitializationDirectConstructorStatement = "IRVariableInitializationDirectConstructorStatement",
    IRVariableInitializationDirectConstructorWithBoxStatement = "IRVariableInitializationDirectConstructorWithBoxStatement",

    IRVariableAssignmentStatement = "IRVariableAssignmentStatement",
    IRVariableAssignmentDirectInvokeStatement = "IRVariableAssignmentDirectInvokeStatement",
    IRVariableAssignmentDirectInvokeWithImplicitStatement = "IRVariableAssignmentDirectInvokeWithImplicitStatement",
    IRVariableAssignmentDirectConstructorStatement = "IRVariableAssignmentDirectConstructorStatement",
    IRVariableAssignmentDirectConstructorWithBoxStatement = "IRVariableAssignmentDirectConstructorWithBoxStatement",

    IRUpdateLocalDirectStatement = "IRUpdateLocalDirectStatement",
    IRUpdateParamDirectStatement = "IRUpdateParamDirectStatement",

    IRReturnVoidSimpleStatement = "IRReturnVoidSimpleStatement",
    IRReturnValueSimpleStatement = "IRReturnValueSimpleStatement",
    IRReturnDirectInvokeStatement = "IRReturnDirectInvokeStatement",
    IRReturnDirectConstructStatement = "IRReturnDirectConstructStatement",
    IRReturnDirectConstructWithBoxStatement = "IRReturnDirectConstructWithBoxStatement",

    IRVoidInvokeStatement = "IRVoidInvokeStatement",

    IRChkLogicImpliesShortCircuitStatement = "IRChkLogicImpliesShortCircuitStatement",

    IRLogicConditionalStatement = "IRLogicConditionalStatement",

    IRSimpleIfStatement = "IRSimpleIfStatement",
    IRSimpleIfElseStatement = "IRSimpleIfElseStatement",

    IRMatchExactStatement = "IRMatchExactStatement",
    IRMatchGeneralStatement = "IRMatchGeneralStatement",

    IRBlockStatement = "IRBlockStatement",

    IRErrorAdditionBoundsCheckStatement = "IRErrorAdditionBoundsCheckStatement",
    IRErrorSubtractionBoundsCheckStatement = "IRErrorSubtractionBoundsCheckStatement",
    IRErrorMultiplicationBoundsCheckStatement = "IRErrorMultiplicationBoundsCheckStatement",
    IRErrorDivisionByZeroCheckStatement = "IRErrorDivisionByZeroCheckStatement",
    IRErrorTypeAssertionCheckStatement = "IRErrorTypeAssertionCheckStatement",

    IRErrorExhaustiveStatement = "IRErrorExhaustiveStatement",

    IRTypeDeclSizeRangeCheckCStringStatement = "IRTypeDeclSizeRangeCheckCStringStatement",
    IRTypeDeclSizeRangeCheckUnicodeStringStatement = "IRTypeDeclSizeRangeCheckUnicodeStringStatement",
    IRTypeDeclNumericRangeCheckStatement = "IRTypeDeclNumericRangeCheckStatement",
    IRTypeDeclFormatCheckCStringStatement = "IRTypeDeclFormatCheckCStringStatement",
    IRTypeDeclFormatCheckUnicodeStringStatement = "IRTypeDeclFormatCheckUnicodeStringStatement",

    IRTypeDeclInvariantCheckStatement = "IRTypeDeclInvariantCheckStatement",
    IREntityInvariantCheckStatement = "IREntityInvariantCheckStatement",
    IRPreconditionCheckStatement = "IRPreconditionCheckStatement",
    IRPostconditionCheckStatement = "IRPostconditionCheckStatement",

    IRAbortStatement = "IRAbortStatement",
    IRAssertStatement = "IRAssertStatement",
    IRDebugStatement = "IRDebugStatement"
}

abstract class IRStatement {
    readonly tag: IRStatementTag;

    constructor(tag: IRStatementTag) {
        this.tag = tag;
    }

    isTerminalStatement(): boolean { return false; }

    abstract isSimpleStatement(): boolean;

    static jsonEmit_IRStatement(stmt: IRStatement): [string, object] {
        if(stmt instanceof IRNopStatement) {
            return ["NopStatement", IRNopStatement.jsonEmit_IRNopStatement(stmt)];
        }
        else if(stmt instanceof IRTempAssignExpressionStatement) {
            return ["TempAssignExpressionStatement", IRTempAssignExpressionStatement.jsonEmit_IRTempAssignExpressionStatement(stmt)];
        }
        else if(stmt instanceof IRTempAssignStdInvokeStatement) {
            return ["TempAssignStdInvokeStatement", IRTempAssignStdInvokeStatement.jsonEmit_IRTempAssignStdInvokeStatement(stmt)];
        }
        else if(stmt instanceof IRTempAssignRefInvokeStatement) {
            return ["TempAssignRefInvokeStatement", IRTempAssignRefInvokeStatement.jsonEmit_IRTempAssignRefInvokeStatement(stmt)];
        }
        else if(stmt instanceof IRTempAssignDirectConstructorStatement) {
            return ["TempAssignDirectConstructorStatement", IRTempAssignDirectConstructorStatement.jsonEmit_IRTempAssignDirectConstructorStatement(stmt)];
        }
        else if(stmt instanceof IRVariableDeclarationStatement) {
            return ["VariableDeclarationStatement", IRVariableDeclarationStatement.jsonEmit_IRVariableDeclarationStatement(stmt)];
        }
        else if(stmt instanceof IRVariableInitializationStatement) {
            return ["VariableInitializationStatement", IRVariableInitializationStatement.jsonEmit_IRVariableInitializationStatement(stmt)];
        }
        else if(stmt instanceof IRVariableInitializationDirectInvokeStatement) {
            return ["VariableInitializationDirectInvokeStatement", IRVariableInitializationDirectInvokeStatement.jsonEmit_IRVariableInitializationDirectInvokeStatement(stmt)];
        }
        else if(stmt instanceof IRVariableInitializationDirectInvokeWithImplicitStatement) {
            return ["VariableInitializationDirectInvokeWithImplicitStatement", IRVariableInitializationDirectInvokeWithImplicitStatement.jsonEmit_IRVariableInitializationDirectInvokeWithImplicitStatement(stmt)];
        }
        else if(stmt instanceof IRVariableInitializationDirectConstructorStatement) {
            return ["VariableInitializationDirectConstructorStatement", IRVariableInitializationDirectConstructorStatement.jsonEmit_IRVariableInitializationDirectConstructorStatement(stmt)];
        }
        else if(stmt instanceof IRVariableInitializationDirectConstructorWithBoxStatement) {
            return ["VariableInitializationDirectConstructorWithBoxStatement", IRVariableInitializationDirectConstructorWithBoxStatement.jsonEmit_IRVariableInitializationDirectConstructorWithBoxStatement(stmt)];
        }
        else if(stmt instanceof IRVariableAssignmentStatement) {
            return ["VariableAssignmentStatement", IRVariableAssignmentStatement.jsonEmit_IRVariableAssignmentStatement(stmt)];
        }
        else if(stmt instanceof IRVariableAssignmentDirectInvokeStatement) {
            return ["VariableAssignmentDirectInvokeStatement", IRVariableAssignmentDirectInvokeStatement.jsonEmit_IRVariableAssignmentDirectInvokeStatement(stmt)];
        }
        else if(stmt instanceof IRVariableAssignmentDirectInvokeWithImplicitStatement) {
            return ["VariableAssignmentDirectInvokeWithImplicitStatement", IRVariableAssignmentDirectInvokeWithImplicitStatement.jsonEmit_IRVariableAssignmentDirectInvokeWithImplicitStatement(stmt)];
        }
        else if(stmt instanceof IRVariableAssignmentDirectConstructorStatement) {
            return ["VariableAssignmentDirectConstructorStatement", IRVariableAssignmentDirectConstructorStatement.jsonEmit_IRVariableAssignmentDirectConstructorStatement(stmt)];
        }
        else if(stmt instanceof IRVariableAssignmentDirectConstructorWithBoxStatement) {
            return ["VariableAssignmentDirectConstructorWithBoxStatement", IRVariableAssignmentDirectConstructorWithBoxStatement.jsonEmit_IRVariableAssignmentDirectConstructorWithBoxStatement(stmt)];
        }
        else if(stmt instanceof IRUpdateLocalDirectStatement) {
            return ["UpdateLocalDirectStatement", IRUpdateLocalDirectStatement.jsonEmit_IRUpdateLocalDirectStatement(stmt)];
        }
        else if(stmt instanceof IRUpdateParamDirectStatement) {
            return ["UpdateParamDirectStatement", IRUpdateParamDirectStatement.jsonEmit_IRUpdateParamDirectStatement(stmt)];
        }
        else if(stmt instanceof IRReturnVoidSimpleStatement) {
            return ["ReturnVoidSimpleStatement", IRReturnVoidSimpleStatement.jsonEmit_IRReturnVoidSimpleStatement(stmt)];
        }
        else if(stmt instanceof IRReturnValueSimpleStatement) {
            return ["ReturnValueSimpleStatement", IRReturnValueSimpleStatement.jsonEmit_IRReturnValueSimpleStatement(stmt)];
        }
        else if(stmt instanceof IRReturnDirectInvokeStatement) {
            return ["ReturnDirectInvokeStatement", IRReturnDirectInvokeStatement.jsonEmit_IRReturnDirectInvokeStatement(stmt)];
        }
        else if(stmt instanceof IRReturnDirectConstructStatement) {
            return ["ReturnDirectConstructStatement", IRReturnDirectConstructStatement.jsonEmit_IRReturnDirectConstructStatement(stmt)];
        }
        else if(stmt instanceof IRReturnDirectConstructWithBoxStatement) {
            return ["ReturnDirectConstructWithBoxStatement", IRReturnDirectConstructWithBoxStatement.jsonEmit_IRReturnDirectConstructWithBoxStatement(stmt)];
        }
        else if(stmt instanceof IRVoidInvokeStatement) {
            return ["VoidInvokeStatement", IRVoidInvokeStatement.jsonEmit_IRVoidInvokeStatement(stmt)];
        }
        else if(stmt instanceof IRChkLogicImpliesShortCircuitStatement) {
            return ["ChkLogicImpliesShortCircuitStatement", IRChkLogicImpliesShortCircuitStatement.jsonEmit_IRChkLogicImpliesShortCircuitStatement(stmt)];
        }
        else if(stmt instanceof IRLogicConditionalStatement) {
            return ["LogicConditionalStatement", IRLogicConditionalStatement.jsonEmit_IRLogicConditionalStatement(stmt)];
        }
        else if(stmt instanceof IRSimpleIfStatement) {
            return ["SimpleIfStatement", IRSimpleIfStatement.jsonEmit_IRSimpleIfStatement(stmt)];
        }
        else if(stmt instanceof IRSimpleIfElseStatement) {
            return ["SimpleIfElseStatement", IRSimpleIfElseStatement.jsonEmit_IRSimpleIfElseStatement(stmt)];
        }
        else if(stmt instanceof IRMatchExactStatement) {
            return ["MatchExactStatement", IRMatchExactStatement.jsonEmit_IRMatchExactStatement(stmt)];
        }
        else if(stmt instanceof IRMatchGeneralStatement) {
            return ["MatchGeneralStatement", IRMatchGeneralStatement.jsonEmit_IRMatchGeneralStatement(stmt)];
        }
        else if(stmt instanceof IRBlockStatement) {
            return ["BlockStatement", IRBlockStatement.jsonEmit_IRBlockStatement(stmt)];
        }
        else if(stmt instanceof IRErrorAdditionBoundsCheckStatement) {
            return ["ErrorAdditionBoundsCheckStatement", IRErrorAdditionBoundsCheckStatement.jsonEmit_IRErrorAdditionBoundsCheckStatement(stmt)];
        }
        else if(stmt instanceof IRErrorSubtractionBoundsCheckStatement) {
            return ["ErrorSubtractionBoundsCheckStatement", IRErrorSubtractionBoundsCheckStatement.jsonEmit_IRErrorSubtractionBoundsCheckStatement(stmt)];
        }
        else if(stmt instanceof IRErrorMultiplicationBoundsCheckStatement) {
            return ["ErrorMultiplicationBoundsCheckStatement", IRErrorMultiplicationBoundsCheckStatement.jsonEmit_IRErrorMultiplicationBoundsCheckStatement(stmt)];
        }
        else if(stmt instanceof IRErrorDivisionByZeroCheckStatement) {
            return ["ErrorDivisionByZeroCheckStatement", IRErrorDivisionByZeroCheckStatement.jsonEmit_IRErrorDivisionByZeroCheckStatement(stmt)];
        }
        else if(stmt instanceof IRErrorTypeAssertionCheckStatement) {
            return ["ErrorTypeAssertionCheckStatement", IRErrorTypeAssertionCheckStatement.jsonEmit_IRErrorTypeAssertionCheckStatement(stmt)];
        }
        else if(stmt instanceof IRErrorExhaustiveStatement) {
            return ["ErrorExhaustiveStatement", IRErrorExhaustiveStatement.jsonEmit_IRErrorExhaustiveStatement(stmt)];
        }
        else if(stmt instanceof IRTypeDeclSizeRangeCheckCStringStatement) {
            return ["TypeDeclSizeRangeCheckCStringStatement", IRTypeDeclSizeRangeCheckCStringStatement.jsonEmit_IRTypeDeclSizeRangeCheckCStringStatement(stmt)];
        }
        else if(stmt instanceof IRTypeDeclSizeRangeCheckUnicodeStringStatement) {
            return ["TypeDeclSizeRangeCheckUnicodeStringStatement", IRTypeDeclSizeRangeCheckUnicodeStringStatement.jsonEmit_IRTypeDeclSizeRangeCheckUnicodeStringStatement(stmt)];
        }
        else if(stmt instanceof IRTypeDeclNumericRangeCheckStatement) {
            return ["TypeDeclNumericRangeCheckStatement", IRTypeDeclNumericRangeCheckStatement.jsonEmit_IRTypeDeclNumericRangeCheckStatement(stmt)];
        }
        else if(stmt instanceof IRTypeDeclFormatCheckCStringStatement) {
            return ["TypeDeclFormatCheckCStringStatement", IRTypeDeclFormatCheckCStringStatement.jsonEmit_IRTypeDeclFormatCheckCStringStatement(stmt)];
        }
        else if(stmt instanceof IRTypeDeclFormatCheckUnicodeStringStatement) {
            return ["TypeDeclFormatCheckUnicodeStringStatement", IRTypeDeclFormatCheckUnicodeStringStatement.jsonEmit_IRTypeDeclFormatCheckUnicodeStringStatement(stmt)];
        }
        else if(stmt instanceof IRTypeDeclInvariantCheckStatement) {
            return ["TypeDeclInvariantCheckStatement", IRTypeDeclInvariantCheckStatement.jsonEmit_IRTypeDeclInvariantCheckStatement(stmt)];
        }
        else if(stmt instanceof IREntityInvariantCheckStatement) {
            return ["EntityInvariantCheckStatement", IREntityInvariantCheckStatement.jsonEmit_IREntityInvariantCheckStatement(stmt)];
        }
        else if(stmt instanceof IRPreconditionCheckStatement) {
            return ["PreconditionCheckStatement", IRPreconditionCheckStatement.jsonEmit_IRPreconditionCheckStatement(stmt)];
        }
        else if(stmt instanceof IRPostconditionCheckStatement) {
            return ["PostconditionCheckStatement", IRPostconditionCheckStatement.jsonEmit_IRPostconditionCheckStatement(stmt)];
        }
        else if(stmt instanceof IRAbortStatement) {
            return ["AbortStatement", IRAbortStatement.jsonEmit_IRAbortStatement(stmt)];
        }
        else if(stmt instanceof IRAssertStatement) {
            return ["AssertStatement", IRAssertStatement.jsonEmit_IRAssertStatement(stmt)];
        }
        else if(stmt instanceof IRDebugStatement) {
            return ["DebugStatement", IRDebugStatement.jsonEmit_IRDebugStatement(stmt)];
        }
        else {
            assert(false, `Unknown IRStatement type -- ${stmt.tag}`)
        }
    }

    static jsonParse_IRStatement(obj: any): IRStatement {
        const kind = obj[0];
        const value = obj[1];

        switch(kind) {
            case "NopStatement": {
                return IRNopStatement.jsonParse_IRNopStatement(value);
            }
            case "TempAssignExpressionStatement": {
                return IRTempAssignExpressionStatement.jsonParse_IRTempAssignExpressionStatement(value);
            }
            case "TempAssignStdInvokeStatement": {
                return IRTempAssignStdInvokeStatement.jsonParse_IRTempAssignStdInvokeStatement(value);
            }
            case "TempAssignRefInvokeStatement": {
                return IRTempAssignRefInvokeStatement.jsonParse_IRTempAssignRefInvokeStatement(value);
            }
            case "TempAssignDirectConstructorStatement": {
                return IRTempAssignDirectConstructorStatement.jsonParse_IRTempAssignDirectConstructorStatement(value);
            }
            case "VariableDeclarationStatement": {
                return IRVariableDeclarationStatement.jsonParse_IRVariableDeclarationStatement(value);
            }
            case "VariableInitializationStatement": {
                return IRVariableInitializationStatement.jsonParse_IRVariableInitializationStatement(value);
            }
            case "VariableInitializationDirectInvokeStatement": {
                return IRVariableInitializationDirectInvokeStatement.jsonParse_IRVariableInitializationDirectInvokeStatement(value);
            }
            case "VariableInitializationDirectInvokeWithImplicitStatement": {
                return IRVariableInitializationDirectInvokeWithImplicitStatement.jsonParse_IRVariableInitializationDirectInvokeWithImplicitStatement(value);
            }
            case "VariableInitializationDirectConstructorStatement": {
                return IRVariableInitializationDirectConstructorStatement.jsonParse_IRVariableInitializationDirectConstructorStatement(value);
            }
            case "VariableInitializationDirectConstructorWithBoxStatement": {
                return IRVariableInitializationDirectConstructorWithBoxStatement.jsonParse_IRVariableInitializationDirectConstructorWithBoxStatement(value);
            }
            case "VariableAssignmentStatement": {
                return IRVariableAssignmentStatement.jsonParse_IRVariableAssignmentStatement(value);
            }
            case "VariableAssignmentDirectInvokeStatement": {
                return IRVariableAssignmentDirectInvokeStatement.jsonParse_IRVariableAssignmentDirectInvokeStatement(value);
            }
            case "VariableAssignmentDirectInvokeWithImplicitStatement": {
                return IRVariableAssignmentDirectInvokeWithImplicitStatement.jsonParse_IRVariableAssignmentDirectInvokeWithImplicitStatement(value);
            }
            case "VariableAssignmentDirectConstructorStatement": {
                return IRVariableAssignmentDirectConstructorStatement.jsonParse_IRVariableAssignmentDirectConstructorStatement(value);
            }
            case "VariableAssignmentDirectConstructorWithBoxStatement": {
                return IRVariableAssignmentDirectConstructorWithBoxStatement.jsonParse_IRVariableAssignmentDirectConstructorWithBoxStatement(value);
            }
            case "UpdateLocalDirectStatement": {
                return IRUpdateLocalDirectStatement.jsonParse_IRUpdateLocalDirectStatement(value);
            }
            case "UpdateParamDirectStatement": {
                return IRUpdateParamDirectStatement.jsonParse_IRUpdateParamDirectStatement(value);
            }
            case "ReturnVoidSimpleStatement": {
                return IRReturnVoidSimpleStatement.jsonParse_IRReturnVoidSimpleStatement(value);
            }
            case "ReturnValueSimpleStatement": {
                return IRReturnValueSimpleStatement.jsonParse_IRReturnValueSimpleStatement(value);
            }
            case "ReturnDirectInvokeStatement": {
                return IRReturnDirectInvokeStatement.jsonParse_IRReturnDirectInvokeStatement(value);
            }
            case "ReturnDirectConstructStatement": {
                return IRReturnDirectConstructStatement.jsonParse_IRReturnDirectConstructStatement(value);
            }
            case "ReturnDirectConstructWithBoxStatement": {
                return IRReturnDirectConstructWithBoxStatement.jsonParse_IRReturnDirectConstructWithBoxStatement(value);
            }
            case "VoidInvokeStatement": {
                return IRVoidInvokeStatement.jsonParse_IRVoidInvokeStatement(value);
            }
            case "ChkLogicImpliesShortCircuitStatement": {
                return IRChkLogicImpliesShortCircuitStatement.jsonParse_IRChkLogicImpliesShortCircuitStatement(value);
            }
            case "LogicConditionalStatement": {
                return IRLogicConditionalStatement.jsonParse_IRLogicConditionalStatement(value);
            }
            case "SimpleIfStatement": {
                return IRSimpleIfStatement.jsonParse_IRSimpleIfStatement(value);
            }
            case "SimpleIfElseStatement": {
                return IRSimpleIfElseStatement.jsonParse_IRSimpleIfElseStatement(value);
            }
            case "MatchExactStatement": {
                return IRMatchExactStatement.jsonParse_IRMatchExactStatement(value);
            }
            case "MatchGeneralStatement": {
                return IRMatchGeneralStatement.jsonParse_IRMatchGeneralStatement(value);
            }
            case "BlockStatement": {
                return IRBlockStatement.jsonParse_IRBlockStatement(value);
            }
            case "ErrorAdditionBoundsCheckStatement": {
                return IRErrorAdditionBoundsCheckStatement.jsonParse_IRErrorAdditionBoundsCheckStatement(value);
            }
            case "ErrorSubtractionBoundsCheckStatement": {
                return IRErrorSubtractionBoundsCheckStatement.jsonParse_IRErrorSubtractionBoundsCheckStatement(value);
            }
            case "ErrorMultiplicationBoundsCheckStatement": {
                return IRErrorMultiplicationBoundsCheckStatement.jsonParse_IRErrorMultiplicationBoundsCheckStatement(value);
            }
            case "ErrorDivisionByZeroCheckStatement": {
                return IRErrorDivisionByZeroCheckStatement.jsonParse_IRErrorDivisionByZeroCheckStatement(value);
            }
            case "ErrorTypeAssertionCheckStatement": {
                return IRErrorTypeAssertionCheckStatement.jsonParse_IRErrorTypeAssertionCheckStatement(value);
            }
            case "ErrorExhaustiveStatement": {
                return IRErrorExhaustiveStatement.jsonParse_IRErrorExhaustiveStatement(value);
            }
            case "TypeDeclSizeRangeCheckCStringStatement": {
                return IRTypeDeclSizeRangeCheckCStringStatement.jsonParse_IRTypeDeclSizeRangeCheckCStringStatement(value);
            }
            case "TypeDeclSizeRangeCheckUnicodeStringStatement": {
                return IRTypeDeclSizeRangeCheckUnicodeStringStatement.jsonParse_IRTypeDeclSizeRangeCheckUnicodeStringStatement(value);
            }
            case "TypeDeclNumericRangeCheckStatement": {
                return IRTypeDeclNumericRangeCheckStatement.jsonParse_IRTypeDeclNumericRangeCheckStatement(value);
            }
            case "TypeDeclFormatCheckCStringStatement": {
                return IRTypeDeclFormatCheckCStringStatement.jsonParse_IRTypeDeclFormatCheckCStringStatement(value);
            }
            case "TypeDeclFormatCheckUnicodeStringStatement": {
                return IRTypeDeclFormatCheckUnicodeStringStatement.jsonParse_IRTypeDeclFormatCheckUnicodeStringStatement(value);
            }
            case "TypeDeclInvariantCheckStatement": {
                return IRTypeDeclInvariantCheckStatement.jsonParse_IRTypeDeclInvariantCheckStatement(value);
            }
            case "EntityInvariantCheckStatement": {
                return IREntityInvariantCheckStatement.jsonParse_IREntityInvariantCheckStatement(value);
            }
            case "PreconditionCheckStatement": {
                return IRPreconditionCheckStatement.jsonParse_IRPreconditionCheckStatement(value);
            }
            case "PostconditionCheckStatement": {
                return IRPostconditionCheckStatement.jsonParse_IRPostconditionCheckStatement(value);
            }
            case "AbortStatement": {
                return IRAbortStatement.jsonParse_IRAbortStatement(value);
            }
            case "AssertStatement": {
                return IRAssertStatement.jsonParse_IRAssertStatement(value);
            }
            case "DebugStatement": {
                return IRDebugStatement.jsonParse_IRDebugStatement(value);
            }
            default: {
                throw new Error(`Unknown statement type: ${kind}`);
            }
        }
    }
}

/* This class represents statements that are atomic (line statements) and don't have control flow or sub blocks */
abstract class IRAtomicStatement extends IRStatement {
    constructor(tag: IRStatementTag) {
        super(tag);
    }

    static jsonEmit_IRAtomicStatement(stmt: IRAtomicStatement): [string, object] {
        return IRStatement.jsonEmit_IRStatement(stmt);
    }

    static jsonParse_IRAtomicStatement(obj: any): IRStatement {
        return IRStatement.jsonParse_IRStatement(obj);
    }
}

/* Represent temporary variable assignment statements */
abstract class IRTempAssignStatement extends IRAtomicStatement {
    readonly ttype: IRTypeSignature;
    readonly tvid: number;

    constructor(tag: IRStatementTag, tvid: number, ttype: IRTypeSignature) {
        super(tag);
        this.tvid = tvid;
        this.ttype = ttype;
    }

    static jsonEmit_IRTempAssignStatement(stmt: IRTempAssignStatement): [string, object] {
        return IRStatement.jsonEmit_IRStatement(stmt);
    }

    static jsonParse_IRTempAssignStatement(obj: any): IRTempAssignStatement {
        return IRStatement.jsonParse_IRStatement(obj) as IRTempAssignStatement;
    }

    static jsonEmitMeta_IRTempAssignStatement(stmt: IRTempAssignStatement): object {
        return {
            ttype: IRTypeSignature.jsonEmit_IRTypeSignature(stmt.ttype),
            tvid: stmt.tvid
        };
    }

    static jsonParseMeta_IRTempAssignStatement(obj: any): [number, IRTypeSignature] {
        return [obj.tvid, IRTypeSignature.jsonParse_IRTypeSignature(obj.ttype)];
    }
}

/* Represent return statement that do not involve any ref/out/out?/inout parameters */
abstract class IRReturnSimpleStatement extends IRAtomicStatement {
    constructor(tag: IRStatementTag) {
        super(tag);
    }

    override isTerminalStatement(): boolean { 
        return true; 
    }

    static jsonEmit_IRReturnSimpleStatement(stmt: IRReturnSimpleStatement): [string, object] {
        return IRStatement.jsonEmit_IRStatement(stmt);
    }

    static jsonParse_IRReturnSimpleStatement(obj: any): IRReturnSimpleStatement {
        return IRStatement.jsonParse_IRStatement(obj) as IRReturnSimpleStatement;
    }
}

/* Explicit error condition checks -- all possible error conditions must be made explicit during flattening */
abstract class IRErrorCheckStatement extends IRAtomicStatement {
    readonly file: string;
    readonly sinfo: IRSourceInfo;

    readonly diagnosticTag: string | undefined;
    readonly checkID: number;

    static assumeCheckID: number = -11;

    constructor(tag: IRStatementTag, file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number) {
        super(tag);
        this.file = file;
        this.sinfo = sinfo;
        this.diagnosticTag = diagnosticTag;
        this.checkID = checkID;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRErrorCheckStatement(stmt: IRErrorCheckStatement): [string, object] {
        return IRStatement.jsonEmit_IRStatement(stmt);
    }

    static jsonParse_IRErrorCheckStatement(obj: any): IRErrorCheckStatement {
        return IRStatement.jsonParse_IRStatement(obj) as IRErrorCheckStatement;
    }

    static jsonEmitMeta_IRErrorCheckStatement(stmt: IRErrorCheckStatement): object {
        return {
            file: stmt.file,
            sinfo: stmt.sinfo.jsonEmit(),
            diagnosticTag: stmt.diagnosticTag === undefined ? null : ["some", stmt.diagnosticTag],
            checkID: stmt.checkID
        };
    }

    static jsonParseMeta_IRErrorCheckStatement(obj: any): [string, IRSourceInfo, string | undefined, number] {
        return [
            obj.file,
            IRSourceInfo.jsonParse(obj.sinfo),
            obj.diagnosticTag === null ? undefined : obj.diagnosticTag[1],
            obj.checkID
        ];
    }
}

abstract class IRErrorBinArithCheckStatement extends IRErrorCheckStatement {
    readonly left: IRImmediateExpression;
    readonly right: IRImmediateExpression;

    readonly optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float";

    constructor(tag: IRStatementTag, file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(tag, file, sinfo, diagnosticTag, checkID);
        this.left = left;
        this.right = right;
        this.optypechk = optypechk;
    }

    static jsonEmit_IRErrorBinArithCheckStatement(stmt: IRErrorBinArithCheckStatement): [string, object] {
        return IRStatement.jsonEmit_IRStatement(stmt);
    }

    static jsonParse_IRErrorBinArithCheckStatement(obj: any): IRErrorBinArithCheckStatement {
        return IRStatement.jsonParse_IRStatement(obj) as IRErrorBinArithCheckStatement;
    }

    static jsonEmitMeta_IRErrorBinArithCheckStatement(stmt: IRErrorBinArithCheckStatement): object {
        return {
            left: IRImmediateExpression.jsonEmit_IRImmediateExpression(stmt.left),
            right: IRImmediateExpression.jsonEmit_IRImmediateExpression(stmt.right),
            optypechk: stmt.optypechk
        };
    }

    static jsonParseMeta_IRErrorBinArithCheckStatement(obj: any): [IRImmediateExpression, IRImmediateExpression, "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float"] {
        return [IRImmediateExpression.jsonParse_IRImmediateExpression(obj.left), IRImmediateExpression.jsonParse_IRImmediateExpression(obj.right), obj.optypechk as "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float"];
    }
}

abstract class IRErrorTypedStringCheckStatement extends IRErrorCheckStatement {
    readonly strexp: IRImmediateExpression;
    
    constructor(tag: IRStatementTag, file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, strexp: IRImmediateExpression) {
        super(tag, file, sinfo, diagnosticTag, checkID);
        this.strexp = strexp;
    }

    static jsonEmit_IRErrorTypedStringCheckStatement(stmt: IRErrorTypedStringCheckStatement): [string, object] {
        return IRStatement.jsonEmit_IRStatement(stmt);
    }

    static jsonParse_IRErrorTypedStringCheckStatement(obj: any): IRErrorTypedStringCheckStatement {
        return IRStatement.jsonParse_IRStatement(obj) as IRErrorTypedStringCheckStatement;
    }

    static jsonEmitMeta_IRErrorTypedStringCheckStatement(stmt: IRErrorTypedStringCheckStatement): object {
        return {
            strexp: IRImmediateExpression.jsonEmit_IRImmediateExpression(stmt.strexp)
        };
    }

    static jsonParseMeta_IRErrorTypedStringCheckStatement(obj: any): [IRImmediateExpression] {
        return [IRImmediateExpression.jsonParse_IRImmediateExpression(obj.strexp)];
    }
}

////////////////////////////////////////
//Our literal expressions are all very safe and will never fail to construct -- if there are possible issues the flattening phase should have emitted and explicit check

class IRLiteralNoneExpression extends IRLiteralExpression {
    constructor() {
        super(IRExpressionTag.IRLiteralNoneExpression);
    }

    static jsonEmit_IRLiteralNoneExpression(exp: IRLiteralNoneExpression): object {
        return {};
    }

    static jsonParse_IRLiteralNoneExpression(obj: any): IRLiteralNoneExpression {
        return new IRLiteralNoneExpression();
    }
}

class IRLiteralBoolExpression extends IRLiteralExpression {
    readonly value: boolean;

    constructor(value: boolean) {
        super(IRExpressionTag.IRLiteralBoolExpression);
        this.value = value;
    }

    static jsonEmit_IRLiteralBoolExpression(exp: IRLiteralBoolExpression): object {
        return {
            value: exp.value
        };
    }

    static jsonParse_IRLiteralBoolExpression(obj: any): IRLiteralBoolExpression {
        return new IRLiteralBoolExpression(obj.value);
    }
}
    
abstract class IRLiteralIntegralNumberExpression extends IRLiteralExpression {
    readonly value: string;

    constructor(tag: IRExpressionTag, value: string) {
        super(tag);
        this.value = value;
    }

    static jsonEmit_IRLiteralIntegralNumberExpression(exp: IRLiteralIntegralNumberExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(exp);
    }

    static jsonParse_IRLiteralIntegralNumberExpression(obj: any): IRLiteralIntegralNumberExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRLiteralIntegralNumberExpression;
    }
}

class IRLiteralNatExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralNatExpression, value);
    }

    static jsonEmit_IRLiteralNatExpression(exp: IRLiteralNatExpression): object {
        return {
            value: exp.value.slice(0, -1)
        };
    }

    static jsonParse_IRLiteralNatExpression(obj: any): IRLiteralNatExpression {
        return new IRLiteralNatExpression(`${obj.value}n`);
    }
}

class IRLiteralIntExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralIntExpression, value);
    }

    static jsonEmit_IRLiteralIntExpression(exp: IRLiteralIntExpression): object {
        return {
            value: exp.value.slice(0, -1)
        };
    }

    static jsonParse_IRLiteralIntExpression(obj: any): IRLiteralIntExpression {
        return new IRLiteralIntExpression(`${obj.value}i`);
    }
}

class IRLiteralChkNatExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralChkNatExpression, value);
    }

    static jsonEmit_IRLiteralChkNatExpression(exp: IRLiteralChkNatExpression): object {
        return {
            value: exp.value.slice(0, -1)
        };
    }

    static jsonParse_IRLiteralChkNatExpression(obj: any): IRLiteralChkNatExpression {
        return new IRLiteralChkNatExpression(`${obj.value}N`);
    }
}

class IRLiteralChkIntExpression extends IRLiteralIntegralNumberExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralChkIntExpression, value);
    }

    static jsonEmit_IRLiteralChkIntExpression(exp: IRLiteralChkIntExpression): object {
        return {
            value: exp.value.slice(0, -1)
        };
    }

    static jsonParse_IRLiteralChkIntExpression(obj: any): IRLiteralChkIntExpression {
        return new IRLiteralChkIntExpression(`${obj.value}I`);
    }
}

class IRLiteralRationalExpression extends IRLiteralExpression {
    readonly numerator: string;
    readonly denominator: string;

    constructor(numerator: string, denominator: string) {
        super(IRExpressionTag.IRLiteralRationalExpression);
        this.numerator = numerator;
        this.denominator = denominator;
    }

    static jsonEmit_IRLiteralRationalExpression(exp: IRLiteralRationalExpression): object {
        return {
            numerator: exp.numerator,
            denominator: exp.denominator
        };
    }

    static jsonParse_IRLiteralRationalExpression(obj: any): IRLiteralRationalExpression {
        assert(false, "TODO -- need to check this");
    }
}

abstract class IRLiteralFloatingPointExpression extends IRLiteralExpression {
    readonly value: string;

    constructor(tag: IRExpressionTag, value: string) {
        super(tag);
        this.value = value;
    }
}

class IRLiteralFloatExpression extends IRLiteralFloatingPointExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralFloatExpression, value);
    }

    static jsonEmit_IRLiteralFloatExpression(exp: IRLiteralFloatExpression): object {
        return {
            value: exp.value
        };
    }

    static jsonParse_IRLiteralFloatExpression(obj: any): IRLiteralFloatExpression {
        return new IRLiteralFloatExpression(`${obj.value}f`);
    }
}

class IRLiteralDecimalExpression extends IRLiteralFloatingPointExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralDecimalExpression, value);
    }

    static jsonEmit_IRLiteralDecimalExpression(exp: IRLiteralDecimalExpression): object {
        assert(false, "IRLiteralDecimalExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralDecimalExpression(obj: any): IRLiteralDecimalExpression {
        assert(false, "IRLiteralDecimalExpression.jsonParse not implemented");
    }
}

class IRLiteralDecimalDegreeExpression extends IRLiteralFloatingPointExpression {
    constructor(value: string) {
        super(IRExpressionTag.IRLiteralDecimalDegreeExpression, value);
    }

    static jsonEmit_IRLiteralDecimalDegreeExpression(exp: IRLiteralDecimalDegreeExpression): object {
        assert(false, "IRLiteralDecimalDegreeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralDecimalDegreeExpression(obj: any): IRLiteralDecimalDegreeExpression {
        assert(false, "IRLiteralDecimalDegreeExpression.jsonParse not implemented");
    }
}

class IRLiteralLatLongCoordinateExpression extends IRLiteralExpression {
    readonly latitude: string;
    readonly longitude: string;

    constructor(latitude: string, longitude: string) {
        super(IRExpressionTag.IRLiteralLatLongCoordinateExpression);
        this.latitude = latitude;
        this.longitude = longitude;
    }

    static jsonEmit_IRLiteralLatLongCoordinateExpression(exp: IRLiteralLatLongCoordinateExpression): object {
        assert(false, "IRLiteralLatLongCoordinateExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralLatLongCoordinateExpression(obj: any): IRLiteralLatLongCoordinateExpression {
        assert(false, "IRLiteralLatLongCoordinateExpression.jsonParse not implemented");
    }
}

class IRLiteralComplexExpression extends IRLiteralExpression {
    readonly real: string;
    readonly imaginary: string;

    constructor(real: string, imaginary: string) {
        super(IRExpressionTag.IRLiteralComplexExpression);
        this.real = real;
        this.imaginary = imaginary;
    }

    static jsonEmit_IRLiteralComplexExpression(exp: IRLiteralComplexExpression): object {
        assert(false, "IRLiteralComplexExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralComplexExpression(obj: any): IRLiteralComplexExpression {
        assert(false, "IRLiteralComplexExpression.jsonParse not implemented");
    }
}

class IRLiteralByteBufferExpression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralByteBufferExpression);
        this.bytes = bytes;
    }

    static jsonEmit_IRLiteralByteBufferExpression(exp: IRLiteralByteBufferExpression): object {
        assert(false, "IRLiteralByteBufferExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralByteBufferExpression(obj: any): IRLiteralByteBufferExpression {
        assert(false, "IRLiteralByteBufferExpression.jsonParse not implemented");
    }
}

class IRLiteralUUIDv4Expression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralUUIDv4Expression);
        this.bytes = bytes;
    }

    static jsonEmit_IRLiteralUUIDv4Expression(exp: IRLiteralUUIDv4Expression): object {
        assert(false, "IRLiteralUUIDv4Expression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralUUIDv4Expression(obj: any): IRLiteralUUIDv4Expression {
        assert(false, "IRLiteralUUIDv4Expression.jsonParse not implemented");
    }
}

class IRLiteralUUIDv7Expression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralUUIDv7Expression);
        this.bytes = bytes;
    }

    static jsonEmit_IRLiteralUUIDv7Expression(exp: IRLiteralUUIDv7Expression): object {
        assert(false, "IRLiteralUUIDv7Expression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralUUIDv7Expression(obj: any): IRLiteralUUIDv7Expression {
        assert(false, "IRLiteralUUIDv7Expression.jsonParse not implemented");
    }
}

class IRLiteralSHAContentHashExpression extends IRLiteralExpression {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralSHAContentHashExpression);
        this.bytes = bytes;
    }

    static jsonEmit_IRLiteralSHAContentHashExpression(exp: IRLiteralSHAContentHashExpression): object {
        assert(false, "IRLiteralSHAContentHashExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralSHAContentHashExpression(obj: any): IRLiteralSHAContentHashExpression {
        assert(false, "IRLiteralSHAContentHashExpression.jsonParse not implemented");
    }
}

class IRDateRepresentation {
    readonly year: number; //1900 to 2299
    readonly month: number;
    readonly day: number;

    constructor(year: number, month: number, day: number) {
        this.year = year;
        this.month = month;
        this.day = day;
    }

    static jsonEmit_IRDateRepresentation(exp: IRDateRepresentation): object {
        assert(false, "IRDateRepresentation.jsonEmit not implemented");
    }

    static jsonParse_IRDateRepresentation(obj: any): IRDateRepresentation {
        assert(false, "IRDateRepresentation.jsonParse not implemented");
    }
}

class IRTimeRepresentation {
    readonly hour: number;
    readonly minute: number;
    readonly second: number;

    constructor(hour: number, minute: number, second: number) {
        this.hour = hour;
        this.minute = minute;
        this.second = second;
    }

    static jsonEmit_IRTimeRepresentation(exp: IRTimeRepresentation): object {
        assert(false, "IRTimeRepresentation.jsonEmit not implemented");
    }

    static jsonParse_IRTimeRepresentation(obj: any): IRTimeRepresentation {
        assert(false, "IRTimeRepresentation.jsonParse not implemented");
    }
}

class IRLiteralTZDateTimeExpression extends IRLiteralExpression {
    readonly date: IRDateRepresentation;
    readonly time: IRTimeRepresentation;
    readonly timezone: string; //IANA timezone as well as freeform with printable ascii
    
    constructor(date: IRDateRepresentation, time: IRTimeRepresentation, timezone: string) {
        super(IRExpressionTag.IRLiteralTZDateTimeExpression);
        this.date = date;
        this.time = time;
        this.timezone = timezone;
    }

    static jsonEmit_IRLiteralTZDateTimeExpression(exp: IRLiteralTZDateTimeExpression): object {
        assert(false, "IRLiteralTZDateTimeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralTZDateTimeExpression(obj: any): IRLiteralTZDateTimeExpression {
        assert(false, "IRLiteralTZDateTimeExpression.jsonParse not implemented");
    }
}

class IRLiteralTAITimeExpression extends IRLiteralExpression {
    readonly date: IRDateRepresentation;
    readonly time: IRTimeRepresentation;

    constructor(date: IRDateRepresentation, time: IRTimeRepresentation) {
        super(IRExpressionTag.IRLiteralTAITimeExpression);
        this.date = date;
        this.time = time;
    }

    static jsonEmit_IRLiteralTAITimeExpression(exp: IRLiteralTAITimeExpression): object {
        assert(false, "IRLiteralTAITimeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralTAITimeExpression(obj: any): IRLiteralTAITimeExpression {
        assert(false, "IRLiteralTAITimeExpression.jsonParse not implemented");
    }
}

class IRLiteralPlainDateExpression extends IRLiteralExpression {
    readonly date: IRDateRepresentation;

    constructor(date: IRDateRepresentation) {
        super(IRExpressionTag.IRLiteralPlainDateExpression);
        this.date = date;
    }

    static jsonEmit_IRLiteralPlainDateExpression(exp: IRLiteralPlainDateExpression): object {
        assert(false, "IRLiteralPlainDateExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralPlainDateExpression(obj: any): IRLiteralPlainDateExpression {
        assert(false, "IRLiteralPlainDateExpression.jsonParse not implemented");
    }
}

class IRLiteralPlainTimeExpression extends IRLiteralExpression {
    readonly time: IRTimeRepresentation;

    constructor(time: IRTimeRepresentation) {
        super(IRExpressionTag.IRLiteralPlainTimeExpression);
        this.time = time;
    }

    static jsonEmit_IRLiteralPlainTimeExpression(exp: IRLiteralPlainTimeExpression): object {
        assert(false, "IRLiteralPlainTimeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralPlainTimeExpression(obj: any): IRLiteralPlainTimeExpression {
        assert(false, "IRLiteralPlainTimeExpression.jsonParse not implemented");
    }
}

class IRLiteralLogicalTimeExpression extends IRLiteralExpression {
    readonly ticks: string;
    
    constructor(ticks: string) {
        super(IRExpressionTag.IRLiteralLogicalTimeExpression);
        this.ticks = ticks;
    }

    static jsonEmit_IRLiteralLogicalTimeExpression(exp: IRLiteralLogicalTimeExpression): object {
        assert(false, "IRLiteralLogicalTimeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralLogicalTimeExpression(obj: any): IRLiteralLogicalTimeExpression {
        assert(false, "IRLiteralLogicalTimeExpression.jsonParse not implemented");
    }
}

class IRLiteralISOTimeStampExpression extends IRLiteralExpression {
    readonly date: IRDateRepresentation;
    readonly time: IRTimeRepresentation;
    readonly milliseconds: number;

    constructor(date: IRDateRepresentation, time: IRTimeRepresentation, milliseconds: number) {
        super(IRExpressionTag.IRLiteralISOTimeStampExpression);
        this.date = date;
        this.time = time;
        this.milliseconds = milliseconds;
    }

    static jsonEmit_IRLiteralISOTimeStampExpression(exp: IRLiteralISOTimeStampExpression): object {
        assert(false, "IRLiteralISOTimeStampExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralISOTimeStampExpression(obj: any): IRLiteralISOTimeStampExpression {
        assert(false, "IRLiteralISOTimeStampExpression.jsonParse not implemented");
    }
}

class IRDeltaDateRepresentation {
    readonly years: number;
    readonly months: number;
    readonly days: number;

    constructor(years: number, months: number, days: number) {
        this.years = years;
        this.months = months;
        this.days = days;
    }

    static jsonEmit_IRDeltaDateRepresentation(exp: IRDeltaDateRepresentation): object {
        assert(false, "IRDeltaDateRepresentation.jsonEmit not implemented");
    }

    static jsonParse_IRDeltaDateRepresentation(obj: any): IRDeltaDateRepresentation {
        assert(false, "IRDeltaDateRepresentation.jsonParse not implemented");
    }
}

class IRDeltaTimeRepresentation {
    readonly hours: number;
    readonly minutes: number;
    readonly seconds: number;

    constructor(hours: number, minutes: number, seconds: number) {
        this.hours = hours;
        this.minutes = minutes;
        this.seconds = seconds;
    }

    static jsonEmit_IRDeltaTimeRepresentation(exp: IRDeltaTimeRepresentation): object {
        assert(false, "IRDeltaTimeRepresentation.jsonEmit not implemented");
    }

    static jsonParse_IRDeltaTimeRepresentation(obj: any): IRDeltaTimeRepresentation {
        assert(false, "IRDeltaTimeRepresentation.jsonParse not implemented");
    }
}

class IRLiteralDeltaDateTimeExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly deltadate: IRDeltaDateRepresentation;
    readonly deltatime: IRDeltaTimeRepresentation;

    constructor(sign: "+" | "-", deltadate: IRDeltaDateRepresentation, deltatime: IRDeltaTimeRepresentation) {
        super(IRExpressionTag.IRLiteralDeltaDateTimeExpression);
        this.sign = sign;
        this.deltadate = deltadate;
        this.deltatime = deltatime;
    }

    static jsonEmit_IRLiteralDeltaDateTimeExpression(exp: IRLiteralDeltaDateTimeExpression): object {
        assert(false, "IRLiteralDeltaDateTimeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralDeltaDateTimeExpression(obj: any): IRLiteralDeltaDateTimeExpression {
        assert(false, "IRLiteralDeltaDateTimeExpression.jsonParse not implemented");
    }
}
 
class IRLiteralDeltaISOTimeStampExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly deltadate: IRDeltaDateRepresentation;
    readonly deltatime: IRDeltaTimeRepresentation;
    readonly deltamilliseconds: BigInt;

    constructor(sign: "+" | "-", deltadate: IRDeltaDateRepresentation, deltatime: IRDeltaTimeRepresentation, deltamilliseconds: BigInt) {
        super(IRExpressionTag.IRLiteralDeltaISOTimeStampExpression);
        this.sign = sign;
        this.deltadate = deltadate;
        this.deltatime = deltatime;
        this.deltamilliseconds = deltamilliseconds;
    }

    static jsonEmit_IRLiteralDeltaISOTimeStampExpression(exp: IRLiteralDeltaISOTimeStampExpression): object {
        assert(false, "IRLiteralDeltaISOTimeStampExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralDeltaISOTimeStampExpression(obj: any): IRLiteralDeltaISOTimeStampExpression {
        assert(false, "IRLiteralDeltaISOTimeStampExpression.jsonParse not implemented");
    }
} 

class IRLiteralDeltaSecondsExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly seconds: string;

    constructor(sign: "+" | "-", seconds: string) {
        super(IRExpressionTag.IRLiteralDeltaSecondsExpression);
        this.sign = sign;
        this.seconds = seconds;
    }

    static jsonEmit_IRLiteralDeltaSecondsExpression(exp: IRLiteralDeltaSecondsExpression): object {
        assert(false, "IRLiteralDeltaSecondsExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralDeltaSecondsExpression(obj: any): IRLiteralDeltaSecondsExpression {
        assert(false, "IRLiteralDeltaSecondsExpression.jsonParse not implemented");
    }
}

class IRLiteralDeltaLogicalTimeExpression extends IRLiteralExpression {
    readonly sign: "+" | "-";
    readonly ticks: string;

    constructor(sign: "+" | "-", ticks: string) {
        super(IRExpressionTag.IRLiteralDeltaLogicalTimeExpression);
        this.sign = sign;
        this.ticks = ticks;
    }

    static jsonEmit_IRLiteralDeltaLogicalTimeExpression(exp: IRLiteralDeltaLogicalTimeExpression): object {
        assert(false, "IRLiteralDeltaLogicalTimeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralDeltaLogicalTimeExpression(obj: any): IRLiteralDeltaLogicalTimeExpression {
        assert(false, "IRLiteralDeltaLogicalTimeExpression.jsonParse not implemented");
    }
}

class IRLiteralUnicodeRegexExpression extends IRLiteralExpression {
    readonly regexID: number
    
    constructor(regexID: number) {
        super(IRExpressionTag.IRLiteralUnicodeRegexExpression);
        this.regexID = regexID;
    }

    static jsonEmit_IRLiteralUnicodeRegexExpression(expr: IRLiteralUnicodeRegexExpression): object {
        return {
            regexID: expr.regexID
        };
    }

    static jsonParse_IRLiteralUnicodeRegexExpression(obj: any): IRLiteralUnicodeRegexExpression {
        return new IRLiteralUnicodeRegexExpression(obj.regexID);
    }
}

class IRLiteralCRegexExpression extends IRLiteralExpression {
    readonly regexID: number
    
    constructor(regexID: number) {
        super(IRExpressionTag.IRLiteralCRegexExpression);
        this.regexID = regexID;
    }

    static jsonEmit_IRLiteralCRegexExpression(expr: IRLiteralCRegexExpression): object {
        return {
            regexID: expr.regexID
        };
    }

    static jsonParse_IRLiteralCRegexExpression(obj: any): IRLiteralCRegexExpression {
        return new IRLiteralCRegexExpression(obj.regexID);
    }
}

class IRLiteralByteExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralByteExpression);
        this.value = value;
    }

    static jsonEmit_IRLiteralByteExpression(exp: IRLiteralByteExpression): object {
        return {
            value: exp.value
        };
    }

    static jsonParse_IRLiteralByteExpression(obj: any): IRLiteralByteExpression {
        return new IRLiteralByteExpression(obj.value);
    }
}

class IRLiteralCCharExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralCCharExpression);
        this.value = value;
    }

    static jsonEmit_IRLiteralCCharExpression(exp: IRLiteralCCharExpression): object {
        return {
            value: String.fromCharCode(exp.value)
        };
    }

    static jsonParse_IRLiteralCCharExpression(obj: any): IRLiteralCCharExpression {
        return new IRLiteralCCharExpression(obj.value.codePointAt(0) as number);
    }
}

class IRLiteralUnicodeCharExpression extends IRLiteralExpression {
    readonly value: number;

    constructor(value: number) {
        super(IRExpressionTag.IRLiteralUnicodeCharExpression);
        this.value = value;
    }

    static jsonEmit_IRLiteralUnicodeCharExpression(exp: IRLiteralUnicodeCharExpression): object {
        return {
            value: String.fromCharCode(exp.value)
        };
    }

    static jsonParse_IRLiteralUnicodeCharExpression(obj: any): IRLiteralUnicodeCharExpression {
        return new IRLiteralUnicodeCharExpression(obj.value.codePointAt(0) as number);
    }
}

class IRLiteralCStringExpression extends IRLiteralExpression {
    readonly bytes: number[]; //char bytes

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralCStringExpression);
        this.bytes = bytes;
    }

    static jsonEmit_IRLiteralCStringExpression(exp: IRLiteralCStringExpression): object {
        return {
            chars: exp.bytes
        };
    }

    static jsonParse_IRLiteralCStringExpression(obj: any): IRLiteralCStringExpression {
        return new IRLiteralCStringExpression(obj.chars);
    }
}

class IRLiteralStringExpression extends IRLiteralExpression {
    readonly bytes: number[]; //utf8 bytes

    constructor(bytes: number[]) {
        super(IRExpressionTag.IRLiteralStringExpression);
        this.bytes = bytes;
    }

    static jsonEmit_IRLiteralStringExpression(exp: IRLiteralStringExpression): object {
        return {
            utf8chars: exp.bytes
        };
    }

    static jsonParse_IRLiteralStringExpression(obj: any): IRLiteralStringExpression {
        return new IRLiteralStringExpression(obj.utf8chars);
    }
}

abstract class IRFormatStringComponent {
    static jsonEmit_IRFormatStringComponent(exp: IRFormatStringComponent): [string, object] {
        if (exp instanceof IRFormatStringTextComponent) {
            return ["Assembly::FormatStringTextComponent", IRFormatStringTextComponent.jsonEmit_IRFormatStringTextComponent(exp)];
        } else if (exp instanceof IRFormatStringArgComponent) {
            return ["Assembly::FormatStringArgComponent", IRFormatStringArgComponent.jsonEmit_IRFormatStringArgComponent(exp)];
        } else {
            assert(false, "Unknown IRFormatStringComponent type");
        }
    }

    static jsonParse_IRFormatStringComponent(obj: any): IRFormatStringComponent {
        const tag = obj[0] as string;

        if (tag === "Assembly::FormatStringTextComponent") {
            return IRFormatStringTextComponent.jsonParse_IRFormatStringTextComponent(obj[1]);
        } else if (tag === "Assembly::FormatStringArgComponent") {
            return IRFormatStringArgComponent.jsonParse_IRFormatStringArgComponent(obj[1]);
        } else {
            assert(false, "Unknown IRFormatStringComponent type");
        }
    }
}

class IRFormatStringTextComponent extends IRFormatStringComponent {
    readonly bytes: number[];

    constructor(bytes: number[]) {
        super();
        this.bytes = bytes;
    }

    static jsonEmit_IRFormatStringTextComponent(exp: IRFormatStringTextComponent): object {
        return {
            bytes: exp.bytes
        };
    }

    static jsonParse_IRFormatStringTextComponent(obj: any): IRFormatStringTextComponent {
        return new IRFormatStringTextComponent(obj.bytes);
    }
}

class IRFormatStringArgComponent extends IRFormatStringComponent {
    readonly aidx: number;
    readonly atype: IRTypeSignature;

    constructor(aidx: number, atype: IRTypeSignature) {
        super();
        this.aidx = aidx;
        this.atype = atype;
    }

    static jsonEmit_IRFormatStringArgComponent(exp: IRFormatStringArgComponent): object {
        return {
            aidx: exp.aidx,
            atype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.atype)
        };
    }

    static jsonParse_IRFormatStringArgComponent(obj: any): IRFormatStringArgComponent {
        return new IRFormatStringArgComponent(obj.aidx, IRTypeSignature.jsonParse_IRTypeSignature(obj.atype));
    }
}

class IRLiteralFormatStringExpression extends IRLiteralExpression {
    readonly fmtid: number; //the format string ID assigned during flattening
    readonly fmts: IRFormatStringComponent[];

    constructor(fmtid: number, fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralFormatStringExpression);
        this.fmtid = fmtid;
        this.fmts = fmts;
    }

    static jsonEmit_IRLiteralFormatStringExpression(exp: IRLiteralFormatStringExpression): object {
        return {
            fmtid: exp.fmtid,
            fmts: exp.fmts.map(f => IRFormatStringComponent.jsonEmit_IRFormatStringComponent(f))
        };
    }

    static jsonParse_IRLiteralFormatStringExpression(obj: any): IRLiteralFormatStringExpression {
        return new IRLiteralFormatStringExpression(obj.fmtid, obj.fmts.map((f: any) => IRFormatStringComponent.jsonParse_IRFormatStringComponent(f)));
    }
}

class IRLiteralFormatCStringExpression extends IRLiteralExpression {
    readonly fmtid: number; //the format string ID assigned during flattening
    readonly fmts: IRFormatStringComponent[];

    constructor(fmtid: number, fmts: IRFormatStringComponent[]) {
        super(IRExpressionTag.IRLiteralFormatCStringExpression);
        this.fmtid = fmtid;
        this.fmts = fmts;
    }

    static jsonEmit_IRLiteralFormatCStringExpression(exp: IRLiteralFormatCStringExpression): object {
        return {
            fmtid: exp.fmtid,
            fmts: exp.fmts.map(f => IRFormatStringComponent.jsonEmit_IRFormatStringComponent(f))
        };
    }

    static jsonParse_IRLiteralFormatCStringExpression(obj: any): IRLiteralFormatCStringExpression {
        return new IRLiteralFormatCStringExpression(obj.fmtid, obj.fmts.map((f: any) => IRFormatStringComponent.jsonParse_IRFormatStringComponent(f)));
    }
}

//
//TODO: Path literal expressions here
//

class IRLiteralTypedExpression extends IRLiteralExpression {
    readonly value: IRLiteralExpression;
    readonly constype: IRTypeSignature;

    constructor(value: IRLiteralExpression, constype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralTypedExpression);
        this.value = value;
        this.constype = constype;
    }

    static jsonEmit_IRLiteralTypedExpression(exp: IRLiteralTypedExpression): object {
        return {
            value: IRLiteralExpression.jsonEmit_IRLiteralExpression(exp.value),
            constype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.constype)
        };
    }

    static jsonParse_IRLiteralTypedExpression(obj: any): IRLiteralTypedExpression {
        return new IRLiteralTypedExpression(
            IRLiteralExpression.jsonParse_IRLiteralExpression(obj.value),
            IRTypeSignature.jsonParse_IRTypeSignature(obj.constype)
        );
    }
}

class IRLiteralTypedStringExpression extends IRLiteralExpression {
    readonly bytes: number[];
    readonly constype: IRTypeSignature;

    constructor(bytes: number[], constype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralTypedStringExpression);
        this.bytes = bytes;
        this.constype = constype;
    }
    static jsonEmit_IRLiteralTypedStringExpression(exp: IRLiteralTypedStringExpression): object {
        return {
            bytes: exp.bytes,
            constype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.constype)
        };
    }

    static jsonParse_IRLiteralTypedStringExpression(obj: any): IRLiteralTypedStringExpression {
        return new IRLiteralTypedStringExpression(
            obj.bytes,
            IRTypeSignature.jsonParse_IRTypeSignature(obj.constype)
        );
    }
}

class IRLiteralTypedCStringExpression extends IRLiteralExpression {
    readonly bytes: number[];
    readonly constype: IRTypeSignature;

    constructor(bytes: number[], constype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralTypedCStringExpression);
        this.bytes = bytes;
        this.constype = constype;
    }

    static jsonEmit_IRLiteralTypedCStringExpression(exp: IRLiteralTypedCStringExpression): object {
        return {
            bytes: exp.bytes,
            constype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.constype)
        };
    }

    static jsonParse_IRLiteralTypedCStringExpression(obj: any): IRLiteralTypedCStringExpression {
        return new IRLiteralTypedCStringExpression(
            obj.bytes,
            IRTypeSignature.jsonParse_IRTypeSignature(obj.constype)
        );
    }
}

class IRAccessEnvHasExpression extends IRExpression {
    readonly keybytes: number[];

    constructor(keybytes: number[]) {
        super(IRExpressionTag.IRAccessEnvHasExpression);
        this.keybytes = keybytes;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    static jsonEmit_IRAccessEnvHasExpression(exp: IRAccessEnvHasExpression): object {
        assert(false, "IRAccessEnvHasExpression.jsonEmit not implemented");
    }

    static jsonParse_IRAccessEnvHasExpression(obj: any): IRAccessEnvHasExpression {
        assert(false, "IRAccessEnvHasExpression.jsonParse not implemented");
    }
}

class IRAccessEnvGetExpression extends IRExpression {
    readonly keybytes: number[];

    constructor(keybytes: number[]) {
        super(IRExpressionTag.IRAccessEnvGetExpression);
        this.keybytes = keybytes;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    static jsonEmit_IRAccessEnvGetExpression(exp: IRAccessEnvGetExpression): object {
        assert(false, "IRAccessEnvGetExpression.jsonEmit not implemented");
    }

    static jsonParse_IRAccessEnvGetExpression(obj: any): IRAccessEnvGetExpression {
        assert(false, "IRAccessEnvGetExpression.jsonParse not implemented");
    }
}

class IRAccessEnvTryGetExpression extends IRExpression {
    readonly keybytes: number[];
    readonly oftype: IRTypeSignature;
    readonly optiontype: IRTypeSignature;

    constructor(keybytes: number[], oftype: IRTypeSignature, optiontype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessEnvTryGetExpression);
        this.keybytes = keybytes;
        this.oftype = oftype;
        this.optiontype = optiontype;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    static jsonEmit_IRAccessEnvTryGetExpression(exp: IRAccessEnvTryGetExpression): object {
        assert(false, "IRAccessEnvTryGetExpression.jsonEmit not implemented");
    }

    static jsonParse_IRAccessEnvTryGetExpression(obj: any): IRAccessEnvTryGetExpression {
        assert(false, "IRAccessEnvTryGetExpression.jsonParse not implemented");
    }
}

class IRTaskAccessIDExpression extends IRExpression {
    constructor() {
        super(IRExpressionTag.IRTaskAccessIDExpression);
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    static jsonEmit_IRTaskAccessIDExpression(exp: IRTaskAccessIDExpression): object {
        assert(false, "IRTaskAccessIDExpression.jsonEmit not implemented");
    }

    static jsonParse_IRTaskAccessIDExpression(obj: any): IRTaskAccessIDExpression {
        assert(false, "IRTaskAccessIDExpression.jsonParse not implemented");
    }
}

class IRTaskAccessParentIDExpression extends IRExpression {
    constructor() {
        super(IRExpressionTag.IRTaskAccessParentIDExpression);
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    static jsonEmit_IRTaskAccessParentIDExpression(exp: IRTaskAccessParentIDExpression): object {
        assert(false, "IRTaskAccessParentIDExpression.jsonEmit not implemented");
    }

    static jsonParse_IRTaskAccessParentIDExpression(obj: any): IRTaskAccessParentIDExpression {
        assert(false, "IRTaskAccessParentIDExpression.jsonParse not implemented");
    }
}

class IRAccessConstantExpression extends IRImmediateExpression {
    readonly constkey: string; //flattened identifer names
    
    constructor(constkey: string) {
        super(IRExpressionTag.IRAccessConstantExpression);
        this.constkey = constkey;
    }

    static jsonEmit_IRAccessConstantExpression(exp: IRAccessConstantExpression): object {
        return {
            constkey: exp.constkey
        };
    }

    static jsonParse_IRAccessConstantExpression(obj: any): IRAccessConstantExpression {
        return new IRAccessConstantExpression(obj.constkey);
    }
}

class IRAccessEnumExpression extends IRImmediateExpression {
    readonly tkey: string;
    readonly membername: string;

    constructor(tkey: string, membername: string) {
        super(IRExpressionTag.IRAccessEnumExpression);
        this.tkey = tkey;
        this.membername = membername;
    }

    static jsonEmit_IRAccessEnumExpression(exp: IRAccessEnumExpression): object {
        return {
            tkey: exp.tkey,
            membername: exp.membername
        };
    }

    static jsonParse_IRAccessEnumExpression(obj: any): IRAccessEnumExpression {
        return new IRAccessEnumExpression(obj.tkey, obj.membername);
    }
}

class IRAccessParameterVariableExpression extends IRImmediateExpression {
    readonly pname: string;

    constructor(pname: string) {
        super(IRExpressionTag.IRAccessParameterVariableExpression);
        this.pname = pname;
    }

    static jsonEmit_IRAccessParameterVariableExpression(exp: IRAccessParameterVariableExpression): object {
        return {
            pname: exp.pname
        };
    }

    static jsonParse_IRAccessParameterVariableExpression(obj: any): IRAccessParameterVariableExpression {
        return new IRAccessParameterVariableExpression(obj.pname);
    }
}

class IRAccessLocalVariableExpression extends IRImmediateExpression {
    readonly vname: string;

    constructor(vname: string) {
        super(IRExpressionTag.IRAccessLocalVariableExpression);
        this.vname = vname;
    }

    static jsonEmit_IRAccessLocalVariableExpression(exp: IRAccessLocalVariableExpression): object {
        return {
            vname: exp.vname
        };
    }

    static jsonParse_IRAccessLocalVariableExpression(obj: any): IRAccessLocalVariableExpression {
        return new IRAccessLocalVariableExpression(obj.vname);
    }
}

class IRAccessCapturedVariableExpression extends IRImmediateExpression {
    readonly vname: string;

    constructor(vname: string) {
        super(IRExpressionTag.IRAccessCapturedVariableExpression);
        this.vname = vname;
    }

    static jsonEmit_IRAccessCapturedVariableExpression(exp: IRAccessCapturedVariableExpression): object {
        return {
            vname: exp.vname
        };
    }

    static jsonParse_IRAccessCapturedVariableExpression(obj: any): IRAccessCapturedVariableExpression {
        return new IRAccessCapturedVariableExpression(obj.vname);
    }
}

class IRAccessTempVariableExpression extends IRImmediateExpression {
    readonly tvid: number;

    constructor(tvid: number) {
        super(IRExpressionTag.IRAccessTempVariableExpression);
        this.tvid = tvid;
    }

    static jsonEmit_IRAccessTempVariableExpression(exp: IRAccessTempVariableExpression): object {
        return {
            tvid: exp.tvid
        };
    }

    static jsonParse_IRAccessTempVariableExpression(obj: any): IRAccessTempVariableExpression {
        return new IRAccessTempVariableExpression(obj.tvid);
    }
}

class IRAccessTypeDeclValueExpression extends IRSimpleExpression {
    readonly accesstype: IRNominalTypeSignature;
    readonly exp: IRSimpleExpression;

    constructor(accesstype: IRNominalTypeSignature, exp: IRSimpleExpression) {
        super(IRExpressionTag.IRAccessTypeDeclValueExpression);
        this.accesstype = accesstype;
        this.exp = exp;
    }

    static jsonEmit_IRAccessTypeDeclValueExpression(exp: IRAccessTypeDeclValueExpression): object {
        return {
            accesstype: IRNominalTypeSignature.jsonEmit(exp.accesstype),
            exp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.exp)
        };
    }

    static jsonParse_IRAccessTypeDeclValueExpression(obj: any): IRAccessTypeDeclValueExpression {
        return new IRAccessTypeDeclValueExpression(
            IRNominalTypeSignature.jsonParse(obj.accesstype),
            IRSimpleExpression.jsonParse_IRSimpleExpression(obj.exp)
        );
    }
}

class IRConstructSafeTypeDeclExpression extends IRSimpleExpression {
    readonly constype: IRNominalTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(constype: IRNominalTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructSafeTypeDeclExpression);
        this.constype = constype;
        this.value = value;
    }

    static jsonEmit_IRConstructSafeTypeDeclExpression(exp: IRConstructSafeTypeDeclExpression): object {
        return {
            constype: IRNominalTypeSignature.jsonEmit(exp.constype),
            value: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.value)
        };
    }

    static jsonParse_IRConstructSafeTypeDeclExpression(obj: any): IRConstructSafeTypeDeclExpression {
        return new IRConstructSafeTypeDeclExpression(
            IRNominalTypeSignature.jsonParse(obj.constype),
            IRSimpleExpression.jsonParse_IRSimpleExpression(obj.value)
        );
    }
}

class IRConstructorSomeTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorSomeTypeExpression);
        this.oftype = oftype;
        this.value = value;
    }

    static jsonEmit_IRConstructorSomeTypeExpression(exp: IRConstructorSomeTypeExpression): object {
        assert(false, "IRConstructorSomeTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorSomeTypeExpression(obj: any): IRConstructorSomeTypeExpression {
        assert(false, "IRConstructorSomeTypeExpression.jsonParse not implemented");
    }
}

class IRConstructorOkTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorOkTypeExpression);
        this.oftype = oftype;
        this.value = value;
    }

    static jsonEmit_IRConstructorOkTypeExpression(exp: IRConstructorOkTypeExpression): object {
        assert(false, "IRConstructorOkTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorOkTypeExpression(obj: any): IRConstructorOkTypeExpression {
        assert(false, "IRConstructorOkTypeExpression.jsonParse not implemented");
    }
}

class IRConstructorFailTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorFailTypeExpression);
        this.oftype = oftype;
        this.value = value;
    }

    static jsonEmit_IRConstructorFailTypeExpression(exp: IRConstructorFailTypeExpression): object {
        assert(false, "IRConstructorFailTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorFailTypeExpression(obj: any): IRConstructorFailTypeExpression {
        assert(false, "IRConstructorFailTypeExpression.jsonParse not implemented");
    }
}

class IRConstructorAPISuccessTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorAPISuccessTypeExpression);
        this.oftype = oftype;
        this.value = value;
    }

    static jsonEmit_IRConstructorAPISuccessTypeExpression(exp: IRConstructorAPISuccessTypeExpression): object {
        assert(false, "IRConstructorAPISuccessTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorAPISuccessTypeExpression(obj: any): IRConstructorAPISuccessTypeExpression {
        assert(false, "IRConstructorAPISuccessTypeExpression.jsonParse not implemented");
    }
}

class IRConstructorMapEntryTypeExpression extends IRSimpleExpression {
    readonly oftype: IRTypeSignature;
    readonly key: IRSimpleExpression;
    readonly value: IRSimpleExpression;

    constructor(oftype: IRTypeSignature, key: IRSimpleExpression, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorMapEntryTypeExpression);
        this.oftype = oftype;
        this.key = key;
        this.value = value;
    }

    static jsonEmit_IRConstructorMapEntryTypeExpression(exp: IRConstructorMapEntryTypeExpression): object {
        assert(false, "IRConstructorMapEntryTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorMapEntryTypeExpression(obj: any): IRConstructorMapEntryTypeExpression {
        assert(false, "IRConstructorMapEntryTypeExpression.jsonParse not implemented");
    }
}

//TODO: maybe add a specialized version of this that does boxing to a concept as well
class IRConstructorStandardEntityExpression extends IRConstructExpression {
    readonly values: IRSimpleExpression[];

    constructor(entitytype: IRNominalTypeSignature, values: IRSimpleExpression[]) {
        super(IRExpressionTag.IRConstructorStandardEntityExpression, entitytype);
        this.values = values;
    }

    static jsonEmit_IRConstructorStandardEntityExpression(exp: IRConstructorStandardEntityExpression): object {
        assert(false, "IRConstructorStandardEntityExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorStandardEntityExpression(obj: any): IRConstructorStandardEntityExpression {
        assert(false, "IRConstructorStandardEntityExpression.jsonParse not implemented");
    }
}

//TODO: maybe add a specialized version of this that does boxing to a concept as well
class IRConstructorLambdaExpression extends IRImmediateExpression {
    readonly ltype: IRLambdaParameterPackTypeSignature;
    readonly values: IRImmediateExpression[];
    
    constructor(entitytype: IRLambdaParameterPackTypeSignature, values: IRImmediateExpression[]) {
        super(IRExpressionTag.IRConstructorLambdaExpression);
        this.ltype = entitytype;
        this.values = values;
    }

    static jsonEmit_IRConstructorLambdaExpression(exp: IRConstructorLambdaExpression): object {
        assert(false, "IRConstructorLambdaExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorLambdaExpression(obj: any): IRConstructorLambdaExpression {
        assert(false, "IRConstructorLambdaExpression.jsonParse not implemented");
    }
}

class IRConstructorEListExpression extends IRSimpleExpression {
    readonly eltype: IREListTypeSignature;
    readonly values: IRSimpleExpression[];

    constructor(eltype: IREListTypeSignature, values: IRSimpleExpression[]) {
        super(IRExpressionTag.IRConstructorEListExpression);
        this.eltype = eltype;
        this.values = values;
    }

    static jsonEmit_IRConstructorEListExpression(exp: IRConstructorEListExpression): object {
        return {
            eltype: IREListTypeSignature.jsonEmit(exp.eltype),
            values: exp.values.map((vv) => IRSimpleExpression.jsonEmit_IRSimpleExpression(vv))
        };
    }

    static jsonParse_IRConstructorEListExpression(obj: any): IRConstructorEListExpression {
        return new IRConstructorEListExpression(
            IREListTypeSignature.jsonParse(obj.eltype),
            obj.values.map((vv: any) => IRSimpleExpression.jsonParse_IRSimpleExpression(vv))
        );
    }
}

/* NOTE -- the empty constructor is a simple expression (as it is really a constant) we can place anywhere safely */
class IRConstructorListEmptyExpression extends IRConstructExpression {
    
    constructor(ctype: IRNominalTypeSignature) {
        super(IRExpressionTag.IRConstructorListEmptyExpression, ctype);
    }

    static jsonEmit_IRConstructorListEmptyExpression(exp: IRConstructorListEmptyExpression): object {
        assert(false, "IRConstructorListEmptyExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorListEmptyExpression(obj: any): IRConstructorListEmptyExpression {
        assert(false, "IRConstructorListEmptyExpression.jsonParse not implemented");
    }
}

class IRConstructorListPassthroughExpression extends IRConstructExpression {
    readonly ptl: IRSimpleExpression;

    constructor(ctype: IRNominalTypeSignature, ptl: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructorListPassthroughExpression, ctype);
        this.ptl = ptl;
    }

    static jsonEmit_IRConstructorListPassthroughExpression(exp: IRConstructorListPassthroughExpression): object {
        assert(false, "IRConstructorListPassthroughExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorListPassthroughExpression(obj: any): IRConstructorListPassthroughExpression {
        assert(false, "IRConstructorListPassthroughExpression.jsonParse not implemented");
    }
}

class IRConstructorListSingletonsExpression extends IRConstructExpression {
    readonly elements: IRSimpleExpression[];

    constructor(ctype: IRNominalTypeSignature, elements: IRSimpleExpression[]) {
        super(IRExpressionTag.IRConstructorListSingletonsExpression, ctype);
        this.elements = elements;
    }

    static jsonEmit_IRConstructorListSingletonsExpression(exp: IRConstructorListSingletonsExpression): object {
        assert(false, "IRConstructorListSingletonsExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorListSingletonsExpression(obj: any): IRConstructorListSingletonsExpression {
        assert(false, "IRConstructorListSingletonsExpression.jsonParse not implemented");
    }
}

class IRConstructorListMixedExpression extends IRConstructExpression {
    readonly elements: { kind: "positional" | "directappend" | "spreadappend", value: IRSimpleExpression }[];

    constructor(ctype: IRNominalTypeSignature, elements: { kind: "positional" | "directappend" | "spreadappend", value: IRSimpleExpression }[]) {
        super(IRExpressionTag.IRConstructorListMixedExpression, ctype);
        this.elements = elements;
    }

    static jsonEmit_IRConstructorListMixedExpression(exp: IRConstructorListMixedExpression): object {
        assert(false, "IRConstructorListMixedExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorListMixedExpression(obj: any): IRConstructorListMixedExpression {
        assert(false, "IRConstructorListMixedExpression.jsonParse not implemented");
    }
}

/* NOTE -- the empty constructor is a simple expression (as it is really a constant) we can place anywhere safely */
class IRConstructorMapEmptyExpression extends IRConstructExpression {
    
    constructor(ctype: IRNominalTypeSignature) {
        super(IRExpressionTag.IRConstructorMapEmptyExpression, ctype);
    }

    static jsonEmit_IRConstructorMapEmptyExpression(exp: IRConstructorMapEmptyExpression): object {
        assert(false, "IRConstructorMapEmptyExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorMapEmptyExpression(obj: any): IRConstructorMapEmptyExpression {
        assert(false, "IRConstructorMapEmptyExpression.jsonParse not implemented");
    }
}

class IRConstructorMapSingletonsExpression extends IRConstructExpression {
    readonly elements: IRSimpleExpression[];

    constructor(ctype: IRNominalTypeSignature, elements: IRSimpleExpression[]) {
        super(IRExpressionTag.IRConstructorMapSingletonsExpression, ctype);
        this.elements = elements;
    }
    static jsonEmit_IRConstructorMapSingletonsExpression(exp: IRConstructorMapSingletonsExpression): object {
        assert(false, "IRConstructorMapSingletonsExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructorMapSingletonsExpression(obj: any): IRConstructorMapSingletonsExpression {
        assert(false, "IRConstructorMapSingletonsExpression.jsonParse not implemented");
    }
}

//
//TODO: lots more expression types here
//

class IRAccessFieldSpecialExpression extends IRAccessFieldExpression {
    constructor(eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessFieldSpecialExpression, eexptype, eexp, intype, fieldname, fieldtype);
    }

    static jsonEmit_IRAccessFieldSpecialExpression(exp: IRAccessFieldSpecialExpression): object {
        assert(false, "IRAccessFieldSpecialExpression.jsonEmit not implemented");
    }

    static jsonParse_IRAccessFieldSpecialExpression(obj: any): IRAccessFieldSpecialExpression {
        assert(false, "IRAccessFieldSpecialExpression.jsonParse not implemented");
    }
}

class IRAccessFieldDirectExpression extends IRAccessFieldExpression {
    constructor(eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessFieldDirectExpression, eexptype, eexp, intype, fieldname, fieldtype);
    }

    static jsonEmit_IRAccessFieldDirectExpression(exp: IRAccessFieldDirectExpression): object {
        assert(false, "IRAccessFieldDirectExpression.jsonEmit not implemented");
    }

    static jsonParse_IRAccessFieldDirectExpression(obj: any): IRAccessFieldDirectExpression {
        assert(false, "IRAccessFieldDirectExpression.jsonParse not implemented");
    }
}

class IRAccessFieldVirtualExpression extends IRAccessFieldExpression {
    constructor(eexptype: IRNominalTypeSignature, eexp: IRSimpleExpression, intype: IRNominalTypeSignature, fieldname: string, fieldtype: IRTypeSignature) {
        super(IRExpressionTag.IRAccessFieldVirtualExpression, eexptype, eexp, intype, fieldname, fieldtype);
    }

    static jsonEmit_IRAccessFieldVirtualExpression(exp: IRAccessFieldVirtualExpression): object {
        assert(false, "IRAccessFieldVirtualExpression.jsonEmit not implemented");
    }

    static jsonParse_IRAccessFieldVirtualExpression(obj: any): IRAccessFieldVirtualExpression {
        assert(false, "IRAccessFieldVirtualExpression.jsonParse not implemented");
    }
}

class IRAccessEListIndexExpression extends IRSimpleExpression {
    readonly eltype: IREListTypeSignature;
    readonly eexp: IRSimpleExpression;
    readonly idx: number;

    constructor(eltype: IREListTypeSignature, eexp: IRSimpleExpression, idx: number) {
        super(IRExpressionTag.IRAccessEListIndexExpression);
        this.eltype = eltype;
        this.eexp = eexp;
        this.idx = idx;
    }

    static jsonEmit_IRAccessEListIndexExpression(exp: IRAccessEListIndexExpression): object {
        return {
            eltype: IREListTypeSignature.jsonEmit(exp.eltype),
            eexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.eexp),
            idx: exp.idx
        };
    }

    static jsonParse_IRAccessEListIndexExpression(obj: any): IRAccessEListIndexExpression {
        return new IRAccessEListIndexExpression(
            IREListTypeSignature.jsonParse(obj.eltype),
            IRSimpleExpression.jsonParse_IRSimpleExpression(obj.eexp),
            obj.idx
        );
    }
}

/** Simple invocations functions/methods/lambdas that do not have any special parameters **/
class IRInvokeSimpleExpression extends IRInvokeDirectExpression {
    constructor(ikey: string, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInvokeSimpleExpression, ikey, args);
    }

    static jsonEmit_IRInvokeSimpleExpression(exp: IRInvokeSimpleExpression): object {
        assert(false, "IRInvokeSimpleExpression.jsonEmit not implemented");
    }

    static jsonParse_IRInvokeSimpleExpression(obj: any): IRInvokeSimpleExpression {
        assert(false, "IRInvokeSimpleExpression.jsonParse not implemented");
    }
}

/** Simple invocations functions/methods/lambdas that have any special ref/out/out?/inout parameters **/
class IRInvokeSimpleWithImplicitsExpression extends IRInvokeImplicitsExpression {
    constructor(ikey: string, args: IRSimpleExpression[], implicitidx: number, ivar: string, ivartype: IRTypeSignature, passkind: IRImplicitInvokeArgPassKind) {
        super(IRExpressionTag.IRInvokeSimpleWithImplicitsExpression, ikey, args, implicitidx, ivar, ivartype, passkind);
    }

    static jsonEmit_IRInvokeSimpleWithImplicitsExpression(exp: IRInvokeSimpleWithImplicitsExpression): object {
        assert(false, "IRInvokeSimpleWithImplicitsExpression.jsonEmit not implemented");
    }

    static jsonParse_IRInvokeSimpleWithImplicitsExpression(obj: any): IRInvokeSimpleWithImplicitsExpression {
        assert(false, "IRInvokeSimpleWithImplicitsExpression.jsonParse not implemented");
    }
}

/** Virtual invocations functions/methods/lambdas that do not have any special parameters (arg0 is the receiver) **/
class IRInvokeVirtualSimpleExpression extends IRInvokeDirectExpression {
    readonly rcvr: IRImmediateExpression;

    constructor(ikey: string, rcvr: IRImmediateExpression, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInvokeVirtualSimpleExpression, ikey, args);
        this.rcvr = rcvr;
    }

    static jsonEmit_IRInvokeVirtualSimpleExpression(exp: IRInvokeVirtualSimpleExpression): object {
        assert(false, "IRInvokeVirtualSimpleExpression.jsonEmit not implemented");
    }

    static jsonParse_IRInvokeVirtualSimpleExpression(obj: any): IRInvokeVirtualSimpleExpression {
        assert(false, "IRInvokeVirtualSimpleExpression.jsonParse not implemented");
    }
}

/** Virtual invocations functions/methods/lambdas that have any special ref/out/out?/inout parameters (arg0 is the receiver) **/
class IRInvokeVirtualWithImplicitsExpression extends IRInvokeImplicitsExpression {
    readonly rcvr: IRImmediateExpression;

    constructor(ikey: string, rcvr: IRImmediateExpression, args: IRSimpleExpression[], implicitidx: number, ivar: string, ivartype: IRTypeSignature, passkind: IRImplicitInvokeArgPassKind) {
        super(IRExpressionTag.IRInvokeVirtualWithImplicitsExpression, ikey, args, implicitidx, ivar, ivartype, passkind);
        this.rcvr = rcvr;
    }

    static jsonEmit_IRInvokeVirtualWithImplicitsExpression(exp: IRInvokeVirtualWithImplicitsExpression): object {
        assert(false, "IRInvokeVirtualWithImplicitsExpression.jsonEmit not implemented");
    }

    static jsonParse_IRInvokeVirtualWithImplicitsExpression(obj: any): IRInvokeVirtualWithImplicitsExpression {
        assert(false, "IRInvokeVirtualWithImplicitsExpression.jsonParse not implemented");
    }
}

class IRInvokeCallAgentOrAPIExpression extends IRExpression {
    readonly bname: string;
    readonly bterms: IRTypeSignature[];
    readonly ikey: string;
    readonly args: IRSimpleExpression[];
    readonly external: boolean;
    
    constructor(bname: string, bterms: IRTypeSignature[], ikey: string, args: IRSimpleExpression[], external: boolean) {
        super(IRExpressionTag.IRInvokeCallAgentOrAPIExpression);
        this.bname = bname;
        this.bterms = bterms;
        this.ikey = ikey;
        this.args = args;
        this.external = external;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    static jsonEmit_IRInvokeCallAgentOrAPIExpression(exp: IRInvokeCallAgentOrAPIExpression): object {
        assert(false, "IRInvokeCallAgentOrAPIExpression.jsonEmit not implemented");
    }

    static jsonParse_IRInvokeCallAgentOrAPIExpression(obj: any): IRInvokeCallAgentOrAPIExpression {
        assert(false, "IRInvokeCallAgentOrAPIExpression.jsonParse not implemented");
    }
}

class IRInvokeTaskActionExpression extends IRExpression {
    readonly ikey: string;
    readonly args: IRSimpleExpression[];

    constructor(ikey: string, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInvokeTaskActionExpression);
        this.ikey = ikey;
        this.args = args;
    }

    override isSimpleExpression(): boolean {
        return false;
    }

    static jsonEmit_IRInvokeTaskActionExpression(exp: IRInvokeTaskActionExpression): object {
        assert(false, "IRInvokeTaskActionExpression.jsonEmit not implemented");
    }

    static jsonParse_IRInvokeTaskActionExpression(obj: any): IRInvokeTaskActionExpression {
        assert(false, "IRInvokeTaskActionExpression.jsonParse not implemented");
    }
}

class IRInterpolateFormatCStringExpression extends IRConstructExpression {
    readonly fmtString: IRSimpleExpression;
    readonly args: IRSimpleExpression[];
    
    constructor(fmtString: IRSimpleExpression, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInterpolateFormatCStringExpression, new IRNominalTypeSignature("CString"));
        this.fmtString = fmtString;
        this.args = args;
    }

    static jsonEmit_IRInterpolateFormatCStringExpression(exp: IRInterpolateFormatCStringExpression): object {
        assert(false, "IRInterpolateFormatCStringExpression.jsonEmit not implemented");
    }

    static jsonParse_IRInterpolateFormatCStringExpression(obj: any): IRInterpolateFormatCStringExpression {
        assert(false, "IRInterpolateFormatCStringExpression.jsonParse not implemented");
    }
}

class IRInterpolateFormatStringExpression extends IRConstructExpression {
    readonly fmtString: IRSimpleExpression;
    readonly args: IRSimpleExpression[];
    
    constructor(fmtString: IRSimpleExpression, args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRInterpolateFormatStringExpression, new IRNominalTypeSignature("String"));
        this.fmtString = fmtString;
        this.args = args;
    }

    static jsonEmit_IRInterpolateFormatStringExpression(exp: IRInterpolateFormatStringExpression): object {
        assert(false, "IRInterpolateFormatStringExpression.jsonEmit not implemented");
    }

    static jsonParse_IRInterpolateFormatStringExpression(obj: any): IRInterpolateFormatStringExpression {
        assert(false, "IRInterpolateFormatStringExpression.jsonParse not implemented");
    }
}

abstract class IRUnaryOpExpression extends IRSimpleExpression {
    readonly exp: IRSimpleExpression;
    readonly opertype: IRTypeSignature;

    constructor(tag: IRExpressionTag, exp: IRSimpleExpression, opertype: IRTypeSignature) {
        super(tag);
        this.exp = exp;
        this.opertype = opertype;
    }

    static jsonEmit_IRUnaryOpExpression(exp: IRUnaryOpExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(exp);
    }

    static jsonParse_IRUnaryOpExpression(obj: any): IRUnaryOpExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRUnaryOpExpression;
    }

    static jsonEmitMeta_IRUnaryOpExpression(exp: IRUnaryOpExpression): object {
        return {
            exp: IRExpression.jsonEmit_IRExpression(exp.exp),
            opertype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.opertype)
        };
    }

    static jsonParseMeta_IRUnaryOpExpression(obj: any): [IRSimpleExpression, IRTypeSignature] {
        return [IRExpression.jsonParse_IRExpression(obj.exp) as IRSimpleExpression, IRTypeSignature.jsonParse_IRTypeSignature(obj.opertype)];
    }
}

class IRPrefixNotOpExpression extends IRUnaryOpExpression {
    constructor(exp: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRPrefixNotOpExpression, exp, opertype);
    }

    static jsonEmit_IRPrefixNotOpExpression(exp: IRPrefixNotOpExpression): object {
        const nval = IRUnaryOpExpression.jsonEmitMeta_IRUnaryOpExpression(exp);
        
        return nval;
    }

    static jsonParse_IRPrefixNotOpExpression(obj: any): IRPrefixNotOpExpression {
        const nval = IRUnaryOpExpression.jsonParseMeta_IRUnaryOpExpression(obj);

        return new IRPrefixNotOpExpression(...nval);
    }
}

class IRPrefixNegateOpExpression extends IRUnaryOpExpression {
    constructor(exp: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRPrefixNegateOpExpression, exp, opertype);
    }

    static jsonEmit_IRPrefixNegateOpExpression(exp: IRPrefixNegateOpExpression): object {
        const nval = IRUnaryOpExpression.jsonEmitMeta_IRUnaryOpExpression(exp);
        
        return nval;
    }

    static jsonParse_IRPrefixNegateOpExpression(obj: any): IRPrefixNegateOpExpression {
        const nval = IRUnaryOpExpression.jsonParseMeta_IRUnaryOpExpression(obj);

        return new IRPrefixNegateOpExpression(...nval);
    }
}

class IRPrefixPlusOpExpression extends IRUnaryOpExpression {
    constructor(exp: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRPrefixPlusOpExpression, exp, opertype);
    }

    static jsonEmit_IRPrefixPlusOpExpression(exp: IRPrefixPlusOpExpression): object {
        const nval = IRUnaryOpExpression.jsonEmitMeta_IRUnaryOpExpression(exp);
    
        return nval;
    }

    static jsonParse_IRPrefixPlusOpExpression(obj: any): IRPrefixPlusOpExpression {
        const nval = IRUnaryOpExpression.jsonParseMeta_IRUnaryOpExpression(obj);
    
        return new IRPrefixPlusOpExpression(...nval);
    }
}

abstract class IRBinOpExpression extends IRSimpleExpression {
    readonly left: IRSimpleExpression;
    readonly right: IRSimpleExpression;
    readonly opertype: IRTypeSignature;

    constructor(tag: IRExpressionTag, left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(tag);
        this.left = left;
        this.right = right;
        this.opertype = opertype;
    }

    static jsonEmit_IRBinOpExpression(exp: IRBinOpExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(exp);
    }

    static jsonParse_IRBinOpExpression(obj: any): IRBinOpExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRBinOpExpression;
    }

    static jsonEmitMeta_IRBinOpExpression(exp: IRBinOpExpression): object {
        return {
            left: IRExpression.jsonEmit_IRExpression(exp.left),
            right: IRExpression.jsonEmit_IRExpression(exp.right),
            opertype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.opertype)
        };
    }

    static jsonParseMeta_IRBinOpExpression(obj: any): [IRSimpleExpression, IRSimpleExpression, IRTypeSignature] {
        return [IRSimpleExpression.jsonParse_IRSimpleExpression(obj.left), IRSimpleExpression.jsonParse_IRSimpleExpression(obj.right), IRTypeSignature.jsonParse_IRTypeSignature(obj.opertype)];
    }
}

class IRBinAddExpression extends IRBinOpExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinAddExpression, left, right, opertype);
    }

    static jsonEmit_IRBinAddExpression(exp: IRBinAddExpression): object {
        const nval = IRBinOpExpression.jsonEmitMeta_IRBinOpExpression(exp);
    
        return nval;
    }

    static jsonParse_IRBinAddExpression(obj: any): IRBinAddExpression {
        const nval = IRBinOpExpression.jsonParseMeta_IRBinOpExpression(obj);

        return new IRBinAddExpression(...nval);
    }
}

class IRBinSubExpression extends IRBinOpExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinSubExpression, left, right, opertype);
    }

    static jsonEmit_IRBinSubExpression(exp: IRBinSubExpression): object {
        const nval = IRBinOpExpression.jsonEmitMeta_IRBinOpExpression(exp);
    
        return nval;
    }

    static jsonParse_IRBinSubExpression(obj: any): IRBinSubExpression {
        const nval = IRBinOpExpression.jsonParseMeta_IRBinOpExpression(obj);

        return new IRBinSubExpression(...nval);
    }
}

class IRBinMultExpression extends IRBinOpExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinMultExpression, left, right, opertype);
    }

    static jsonEmit_IRBinMultExpression(exp: IRBinMultExpression): object {
        const nval = IRBinOpExpression.jsonEmitMeta_IRBinOpExpression(exp);
    
        return nval;
    }

    static jsonParse_IRBinMultExpression(obj: any): IRBinMultExpression {
        const nval = IRBinOpExpression.jsonParseMeta_IRBinOpExpression(obj);

        return new IRBinMultExpression(...nval);
    }
}

class IRBinDivExpression extends IRBinOpExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinDivExpression, left, right, opertype);
    }

    static jsonEmit_IRBinDivExpression(exp: IRBinDivExpression): object {
        const nval = IRBinOpExpression.jsonEmitMeta_IRBinOpExpression(exp);
    
        return nval;
    }

    static jsonParse_IRBinDivExpression(obj: any): IRBinDivExpression {
        const nval = IRBinOpExpression.jsonParseMeta_IRBinOpExpression(obj);

        return new IRBinDivExpression(...nval);
    }
}

abstract class IRNumericComparisonExpression extends IRSimpleExpression {
    readonly left: IRSimpleExpression;
    readonly right: IRSimpleExpression;
    readonly opertype: IRTypeSignature;

    constructor(tag: IRExpressionTag, left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(tag);
        this.left = left;
        this.right = right;
        this.opertype = opertype;
    }

    static jsonEmit_IRNumericComparisonExpression(exp: IRNumericComparisonExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(exp);
    }

    static jsonParse_IRNumericComparisonExpression(obj: any): IRNumericComparisonExpression {
        return IRExpression.jsonParse_IRExpression(obj) as IRNumericComparisonExpression;
    }

    static jsonEmitMeta_IRNumericComparisonExpression(exp: IRNumericComparisonExpression): object {
        return {
            left: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.left),
            right: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.right),
            opertype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.opertype)
        };
    }

    static jsonParseMeta_IRNumericComparisonExpression(obj: any): [IRSimpleExpression, IRSimpleExpression, IRTypeSignature] {
        return [IRSimpleExpression.jsonParse_IRSimpleExpression(obj.left), IRSimpleExpression.jsonParse_IRSimpleExpression(obj.right), IRTypeSignature.jsonParse_IRTypeSignature(obj.opertype)];
    }
}

class IRNumericEqExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericEqExpression, left, right, opertype);
    }

    static jsonEmit_IRNumericEqExpression(exp: IRNumericEqExpression): object {
        const nval = IRNumericComparisonExpression.jsonEmitMeta_IRNumericComparisonExpression(exp);

        return nval;
    }
    
    static jsonParse_IRNumericEqExpression(obj: any): IRNumericEqExpression {
        const nval = IRNumericComparisonExpression.jsonParseMeta_IRNumericComparisonExpression(obj);

        return new IRNumericEqExpression(...nval);
    }
}

class IRNumericNeqExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericNeqExpression, left, right, opertype);
    }

    static jsonEmit_IRNumericNeqExpression(exp: IRNumericNeqExpression): object {
        const nval = IRNumericComparisonExpression.jsonEmitMeta_IRNumericComparisonExpression(exp);

        return nval;
    }

    static jsonParse_IRNumericNeqExpression(obj: any): IRNumericNeqExpression {
        const nval = IRNumericComparisonExpression.jsonParseMeta_IRNumericComparisonExpression(obj);

        return new IRNumericNeqExpression(...nval);
    }
}

class IRNumericLessExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericLessExpression, left, right, opertype);
    }

    static jsonEmit_IRNumericLessExpression(exp: IRNumericLessExpression): object {
        const nval = IRNumericComparisonExpression.jsonEmitMeta_IRNumericComparisonExpression(exp);

        return nval;
    }

    static jsonParse_IRNumericLessExpression(obj: any): IRNumericLessExpression {
        const nval = IRNumericComparisonExpression.jsonParseMeta_IRNumericComparisonExpression(obj);

        return new IRNumericLessExpression(...nval);
    }
}

class IRNumericLessEqExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericLessEqExpression, left, right, opertype);
    }

    static jsonEmit_IRNumericLessEqExpression(exp: IRNumericLessEqExpression): object {
        const nval = IRNumericComparisonExpression.jsonEmitMeta_IRNumericComparisonExpression(exp);

        return nval;
    }

    static jsonParse_IRNumericLessEqExpression(obj: any): IRNumericLessEqExpression {
        const nval = IRNumericComparisonExpression.jsonParseMeta_IRNumericComparisonExpression(obj);

        return new IRNumericLessEqExpression(...nval);
    }
}

class IRNumericGreaterExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericGreaterExpression, left, right, opertype);
    }

    static jsonEmit_IRNumericGreaterExpression(exp: IRNumericGreaterExpression): object {
        const nval = IRNumericComparisonExpression.jsonEmitMeta_IRNumericComparisonExpression(exp);

        return nval;
    }

    static jsonParse_IRNumericGreaterExpression(obj: any): IRNumericGreaterExpression {
        const nval = IRNumericComparisonExpression.jsonParseMeta_IRNumericComparisonExpression(obj);

        return new IRNumericGreaterExpression(...nval);
    }
}

class IRNumericGreaterEqExpression extends IRNumericComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRNumericGreaterEqExpression, left, right, opertype);
    }

    static jsonEmit_IRNumericGreaterEqExpression(exp: IRNumericGreaterEqExpression): object {
        const nval = IRNumericComparisonExpression.jsonEmitMeta_IRNumericComparisonExpression(exp);

        return nval;
    }

    static jsonParse_IRNumericGreaterEqExpression(obj: any): IRNumericGreaterEqExpression {
        const nval = IRNumericComparisonExpression.jsonParseMeta_IRNumericComparisonExpression(obj);

        return new IRNumericGreaterEqExpression(...nval);
    }
}

class IRIsNoneOptionExpression extends IRSimpleExpression {
    readonly exp: IRSimpleExpression;
    readonly opttype: IRTypeSignature;

    constructor(exp: IRSimpleExpression, opttype: IRTypeSignature) {
        super(IRExpressionTag.IRIsNoneOptionExpression);
        this.exp = exp;
        this.opttype = opttype;
    }

    static jsonEmit_IRIsNoneOptionExpression(exp: IRIsNoneOptionExpression): object {
        return {
            exp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.exp),
            opttype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.opttype)
        };
    }

    static jsonParse_IRIsNoneOptionExpression(obj: any): IRIsNoneOptionExpression {
        const exp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.exp);
        const opttype = IRTypeSignature.jsonParse_IRTypeSignature(obj.opttype);

        return new IRIsNoneOptionExpression(exp, opttype);
    }
}

class IRIsNotNoneOptionExpression extends IRSimpleExpression {
    readonly exp: IRSimpleExpression;
    readonly opttype: IRTypeSignature;

    constructor(exp: IRSimpleExpression, opttype: IRTypeSignature) {
        super(IRExpressionTag.IRIsNotNoneOptionExpression);
        this.exp = exp;
        this.opttype = opttype;
    }

    static jsonEmit_IRIsNotNoneOptionExpression(exp: IRIsNotNoneOptionExpression): object {
        return {
            exp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.exp),
            opttype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.opttype)
        };
    }

    static jsonParse_IRIsNotNoneOptionExpression(obj: any): IRIsNotNoneOptionExpression {
        const exp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.exp);
        const opttype = IRTypeSignature.jsonParse_IRTypeSignature(obj.opttype);

        return new IRIsNotNoneOptionExpression(exp, opttype);
    }
}

class IRIsOptionEqValueExpression extends IRSimpleExpression {
    readonly optexp: IRSimpleExpression;
    readonly opttype: IRTypeSignature;

    readonly valexp: IRSimpleExpression;
    readonly valtype: IRTypeSignature;

    constructor(optexp: IRSimpleExpression, opttype: IRTypeSignature, valexp: IRSimpleExpression, valtype: IRTypeSignature) {
        super(IRExpressionTag.IRIsOptionEqValueExpression);
        this.optexp = optexp;
        this.opttype = opttype;
        this.valexp = valexp;
        this.valtype = valtype;
    }

    static jsonEmit_IRIsOptionEqValueExpression(exp: IRIsOptionEqValueExpression): object {
        return {
            optexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.optexp),
            opttype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.opttype),
            valexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.valexp),
            valtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.valtype)
        };
    }

    static jsonParse_IRIsOptionEqValueExpression(obj: any): IRIsOptionEqValueExpression {
        const optexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.optexp);
        const opttype = IRTypeSignature.jsonParse_IRTypeSignature(obj.opttype);
        const valexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.valexp);
        const valtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.valtype);

        return new IRIsOptionEqValueExpression(optexp, opttype, valexp, valtype);
    }
}

class IRIsOptionNeqValueExpression extends IRSimpleExpression {
    readonly optexp: IRSimpleExpression;
    readonly opttype: IRTypeSignature;

    readonly valexp: IRSimpleExpression;
    readonly valtype: IRTypeSignature;

    constructor(optexp: IRSimpleExpression, opttype: IRTypeSignature, valexp: IRSimpleExpression, valtype: IRTypeSignature) {
        super(IRExpressionTag.IRIsOptionNeqValueExpression);
        this.optexp = optexp;
        this.opttype = opttype;
        this.valexp = valexp;
        this.valtype = valtype;
    }

    static jsonEmit_IRIsOptionNeqValueExpression(exp: IRIsOptionNeqValueExpression): object {
        return {
            optexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.optexp),
            opttype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.opttype),
            valexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.valexp),
            valtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.valtype)
        };
    }

    static jsonParse_IRIsOptionNeqValueExpression(obj: any): IRIsOptionNeqValueExpression {
        const optexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.optexp);
        const opttype = IRTypeSignature.jsonParse_IRTypeSignature(obj.opttype);
        const valexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.valexp);
        const valtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.valtype);

        return new IRIsOptionNeqValueExpression(optexp, opttype, valexp, valtype);
    }
}

class IRIsSomeEqValueExpression extends IRSimpleExpression {
    readonly someexp: IRSimpleExpression;
    readonly sometype: IRTypeSignature;

    readonly valexp: IRSimpleExpression;
    readonly valtype: IRTypeSignature;

    constructor(someexp: IRSimpleExpression, sometype: IRTypeSignature, valexp: IRSimpleExpression, valtype: IRTypeSignature) {
        super(IRExpressionTag.IRIsSomeEqValueExpression);
        this.someexp = someexp;
        this.sometype = sometype;
        this.valexp = valexp;
        this.valtype = valtype;
    }

    static jsonEmit_IRIsSomeEqValueExpression(exp: IRIsSomeEqValueExpression): object {
        return {
            someexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.someexp),
            sometype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.sometype),
            valexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.valexp),
            valtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.valtype)
        };
    }

    static jsonParse_IRIsSomeEqValueExpression(obj: any): IRIsSomeEqValueExpression {
        const someexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.someexp);
        const sometype = IRTypeSignature.jsonParse_IRTypeSignature(obj.sometype);
        const valexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.valexp);
        const valtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.valtype);

        return new IRIsSomeEqValueExpression(someexp, sometype, valexp, valtype);
    }
}

class IRIsSomeNeqValueExpression extends IRSimpleExpression {
    readonly someexp: IRSimpleExpression;
    readonly sometype: IRTypeSignature;

    readonly valexp: IRSimpleExpression;
    readonly valtype: IRTypeSignature;

    constructor(someexp: IRSimpleExpression, sometype: IRTypeSignature, valexp: IRSimpleExpression, valtype: IRTypeSignature) {
        super(IRExpressionTag.IRIsSomeNeqValueExpression);
        this.someexp = someexp;
        this.sometype = sometype;
        this.valexp = valexp;
        this.valtype = valtype;
    }

    static jsonEmit_IRIsSomeNeqValueExpression(exp: IRIsSomeNeqValueExpression): object {
        return {
            someexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.someexp),
            sometype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.sometype),
            valexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.valexp),
            valtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.valtype)
        };
    }

    static jsonParse_IRIsSomeNeqValueExpression(obj: any): IRIsSomeNeqValueExpression {
        const someexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.someexp);
        const sometype = IRTypeSignature.jsonParse_IRTypeSignature(obj.sometype);
        const valexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.valexp);
        const valtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.valtype);

        return new IRIsSomeNeqValueExpression(someexp, sometype, valexp, valtype);
    }
}

abstract class IRKeyComparisonExpression extends IRSimpleExpression {
    readonly left: IRSimpleExpression;
    readonly right: IRSimpleExpression;
    readonly opertype: IRTypeSignature;

    constructor(tag: IRExpressionTag, left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(tag);
        this.left = left;
        this.right = right;
        this.opertype = opertype;
    }

    static jsonEmit_IRKeyComparisonExpression(exp: IRKeyComparisonExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(exp);
    }

    static jsonParse_IRKeyComparisonExpression(obj: any): IRKeyComparisonExpression{
        return IRExpression.jsonParse_IRExpression(obj) as IRKeyComparisonExpression;
    }

    static jsonEmitMeta_IRKeyComparisonExpression(exp: IRKeyComparisonExpression): object {
        return {
            left: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.left),
            right: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.right),
            opertype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.opertype)
        };
    }

    static jsonParseMeta_IRKeyComparisonExpression(obj: any): [IRSimpleExpression, IRSimpleExpression, IRTypeSignature] {
        return [IRSimpleExpression.jsonParse_IRSimpleExpression(obj.left), IRSimpleExpression.jsonParse_IRSimpleExpression(obj.right), IRTypeSignature.jsonParse_IRTypeSignature(obj.opertype)];
    }
}

class IRBinKeyEqDirectExpression extends IRKeyComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinKeyEqDirectExpression, left, right, opertype);
    }

    static jsonEmit_IRBinKeyEqDirectExpression(exp: IRBinKeyEqDirectExpression): object {
        const nval = IRKeyComparisonExpression.jsonEmitMeta_IRKeyComparisonExpression(exp);

        return nval;
    }

    static jsonParse_IRBinKeyEqDirectExpression(obj: any): IRBinKeyEqDirectExpression {
        const nval = IRKeyComparisonExpression.jsonParseMeta_IRKeyComparisonExpression(obj);

        return new IRBinKeyEqDirectExpression(...nval);
    }
}

class IRBinKeyNeqDirectExpression extends IRKeyComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinKeyNeqDirectExpression, left, right, opertype);
    }

    static jsonEmit_IRBinKeyNeqDirectExpression(exp: IRBinKeyNeqDirectExpression): object {
        const nval = IRKeyComparisonExpression.jsonEmitMeta_IRKeyComparisonExpression(exp);

        return nval;
    }

    static jsonParse_IRBinKeyNeqDirectExpression(obj: any): IRBinKeyNeqDirectExpression {
        const nval = IRKeyComparisonExpression.jsonParseMeta_IRKeyComparisonExpression(obj);

        return new IRBinKeyNeqDirectExpression(...nval);
    }
}

class IRBinKeyLessDirectExpression extends IRKeyComparisonExpression {
    constructor(left: IRSimpleExpression, right: IRSimpleExpression, opertype: IRTypeSignature) {
        super(IRExpressionTag.IRBinKeyLessDirectExpression, left, right, opertype);
    }

    static jsonEmit_IRBinKeyLessDirectExpression(exp: IRBinKeyLessDirectExpression): object {
        const nval = IRKeyComparisonExpression.jsonEmitMeta_IRKeyComparisonExpression(exp);

        return nval;
    }

    static jsonParse_IRBinKeyLessDirectExpression(obj: any): IRBinKeyLessDirectExpression {
        const nval = IRKeyComparisonExpression.jsonParseMeta_IRKeyComparisonExpression(obj);

        return new IRBinKeyLessDirectExpression(...nval);
    }
}

abstract class IRLogicOpExpression extends IRSimpleExpression {
    readonly args: IRSimpleExpression[];

    constructor(tag: IRExpressionTag, args: IRSimpleExpression[]) {
        super(tag);
        this.args = args;
    }

    static jsonEmit_IRLogicOpExpression(exp: IRLogicOpExpression): [string, object] {
        return IRExpression.jsonEmit_IRExpression(exp);
    }

    static jsonParse_IRLogicOpExpression(obj: any): IRLogicOpExpression{
        return IRExpression.jsonParse_IRExpression(obj) as IRLogicOpExpression;
    }

    static jsonEmitMeta_IRLogicOpExpression(exp: IRLogicOpExpression): object {
        return {
            args: exp.args.map((arg) => IRSimpleExpression.jsonEmit_IRSimpleExpression(arg))
        };
    }

    static jsonParseMeta_IRLogicOpExpression(obj: any): [IRSimpleExpression[]] {
        return [obj.args.map((arg: any) => IRSimpleExpression.jsonParse_IRSimpleExpression(arg))];
    }
}

class IRLogicAndExpression extends IRLogicOpExpression {
    constructor(args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRLogicAndExpression, args);
    }

    static jsonEmit_IRLogicAndExpression(exp: IRLogicAndExpression): object {
        const nval = IRLogicOpExpression.jsonEmitMeta_IRLogicOpExpression(exp);

        return nval;
    }

    static jsonParse_IRLogicAndExpression(obj: any): IRLogicAndExpression {
        const nval = IRLogicOpExpression.jsonParseMeta_IRLogicOpExpression(obj);

        return new IRLogicAndExpression(...nval);
    }
}

class IRLogicOrExpression extends IRLogicOpExpression {
    constructor(args: IRSimpleExpression[]) {
        super(IRExpressionTag.IRLogicOrExpression, args);
    }

    static jsonEmit_IRLogicOrExpression(exp: IRLogicOrExpression): object {
        const nval = IRLogicOpExpression.jsonEmitMeta_IRLogicOpExpression(exp);

        return nval;
    }

    static jsonParse_IRLogicOrExpression(obj: any): IRLogicOrExpression {
        const nval = IRLogicOpExpression.jsonParseMeta_IRLogicOpExpression(obj);

        return new IRLogicOrExpression(...nval);
    }
}

class IRLogicSimpleConditionalExpression extends IRSimpleExpression {
    readonly condition: IRSimpleExpression;
    readonly trueexp: IRSimpleExpression;
    readonly falseexp: IRSimpleExpression;

    constructor(condition: IRSimpleExpression, trueexp: IRSimpleExpression, falseexp: IRSimpleExpression) {
        super(IRExpressionTag.IRLogicSimpleConditionalExpression);
        this.condition = condition;
        this.trueexp = trueexp;
        this.falseexp = falseexp;
    }

    static jsonEmit_IRLogicSimpleConditionalExpression(exp: IRLogicSimpleConditionalExpression): object {
        assert(false, "IRLogicSimpleConditionalExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLogicSimpleConditionalExpression(obj: any): IRLogicSimpleConditionalExpression {
        assert(false, "IRLogicSimpleConditionalExpression.jsonParse not implemented");
    }
}

class IRLiteralOptionOfNoneExpression extends IRLiteralExpression {
    readonly opttype: IRTypeSignature;

    constructor(opttype: IRTypeSignature) {
        super(IRExpressionTag.IRLiteralOptionOfNoneExpression);
        this.opttype = opttype;
    }

    static jsonEmit_IRLiteralOptionOfNoneExpression(exp: IRLiteralOptionOfNoneExpression): object {
        assert(false, "IRLiteralOptionOfNoneExpression.jsonEmit not implemented");
    }

    static jsonParse_IRLiteralOptionOfNoneExpression(obj: any): IRLiteralOptionOfNoneExpression {
        assert(false, "IRLiteralOptionOfNoneExpression.jsonParse not implemented");
    }
}

class IRConstructOptionFromSomeExpression extends IRSimpleExpression {
    readonly opttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(opttype: IRTypeSignature, sometype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructOptionFromSomeExpression);
        this.opttype = opttype;
        this.sometype = sometype;
        this.value = value;
    }

    static jsonEmit_IRConstructOptionFromSomeExpression(exp: IRConstructOptionFromSomeExpression): object {
        assert(false, "IRConstructOptionFromSomeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructOptionFromSomeExpression(obj: any): IRConstructOptionFromSomeExpression {
        assert(false, "IRConstructOptionFromSomeExpression.jsonParse not implemented");
    }
}

class IRExtractSomeFromOptionExpression extends IRSimpleExpression {
    readonly opttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(opttype: IRTypeSignature, sometype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractSomeFromOptionExpression);
        this.opttype = opttype;
        this.sometype = sometype;
        this.value = value;
    }

    static jsonEmit_IRExtractSomeFromOptionExpression(exp: IRExtractSomeFromOptionExpression): object {
        assert(false, "IRExtractSomeFromOptionExpression.jsonEmit not implemented");
    }

    static jsonParse_IRExtractSomeFromOptionExpression(obj: any): IRExtractSomeFromOptionExpression {
        assert(false, "IRExtractSomeFromOptionExpression.jsonParse not implemented");
    }
}

class IRExtractSomeValueFromOptionExpression extends IRSimpleExpression {
    readonly opttype: IRTypeSignature;
    readonly sometype: IRTypeSignature;
    readonly ttype : IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(opttype: IRTypeSignature, sometype: IRTypeSignature, ttype : IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractSomeValueFromOptionExpression);
        this.opttype = opttype;
        this.sometype = sometype;
        this.ttype = ttype;
        this.value = value;
    }

    static jsonEmit_IRExtractSomeValueFromOptionExpression(exp: IRExtractSomeValueFromOptionExpression): object {
        assert(false, "IRExtractSomeValueFromOptionExpression.jsonEmit not implemented");
    }

    static jsonParse_IRExtractSomeValueFromOptionExpression(obj: any): IRExtractSomeValueFromOptionExpression {
        assert(false, "IRExtractSomeValueFromOptionExpression.jsonParse not implemented");
    }
}

class IRConstructResultFromOkExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly oktype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, oktype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructResultFromOkExpression);
        this.rtype = rtype;
        this.oktype = oktype;
        this.value = value;
    }

    static jsonEmit_IRConstructResultFromOkExpression(exp: IRConstructResultFromOkExpression): object {
        assert(false, "IRConstructResultFromOkExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructResultFromOkExpression(obj: any): IRConstructResultFromOkExpression {
        assert(false, "IRConstructResultFromOkExpression.jsonParse not implemented");
    }
}

class IRConstructResultFromFailExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly failtype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, failtype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConstructResultFromFailExpression);
        this.rtype = rtype;
        this.failtype = failtype;
        this.value = value;
    }

    static jsonEmit_IRConstructResultFromFailExpression(exp: IRConstructResultFromFailExpression): object {
        assert(false, "IRConstructResultFromFailExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConstructResultFromFailExpression(obj: any): IRConstructResultFromFailExpression {
        assert(false, "IRConstructResultFromFailExpression.jsonParse not implemented");
    }
}

class IRExtractOkFromResultExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly oktype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, oktype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractOkFromResultExpression);
        this.rtype = rtype;
        this.oktype = oktype;
        this.value = value;
    }

    static jsonEmit_IRExtractOkFromResultExpression(exp: IRExtractOkFromResultExpression): object {
        assert(false, "IRExtractOkFromResultExpression.jsonEmit not implemented");
    }

    static jsonParse_IRExtractOkFromResultExpression(obj: any): IRExtractOkFromResultExpression {
        assert(false, "IRExtractOkFromResultExpression.jsonParse not implemented");
    }
}

class IRExtractOkValueFromResultExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly oktype: IRTypeSignature;
    readonly ttype : IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, oktype: IRTypeSignature, ttype : IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractOkValueFromResultExpression);
        this.rtype = rtype;
        this.oktype = oktype;
        this.ttype = ttype;
        this.value = value;
    }

    static jsonEmit_IRExtractOkValueFromResultExpression(exp: IRExtractOkValueFromResultExpression): object {
        assert(false, "IRExtractOkValueFromResultExpression.jsonEmit not implemented");
    }

    static jsonParse_IRExtractOkValueFromResultExpression(obj: any): IRExtractOkValueFromResultExpression {
        assert(false, "IRExtractOkValueFromResultExpression.jsonParse not implemented");
    }
}

class IRExtractFailFromResultExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly failtype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, failtype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractFailFromResultExpression);
        this.rtype = rtype;
        this.failtype = failtype;
        this.value = value;
    }

    static jsonEmit_IRExtractFailFromResultExpression(exp: IRExtractFailFromResultExpression): object {
        assert(false, "IRExtractFailFromResultExpression.jsonEmit not implemented");
    }

    static jsonParse_IRExtractFailFromResultExpression(obj: any): IRExtractFailFromResultExpression {
        assert(false, "IRExtractFailFromResultExpression.jsonParse not implemented");
    }
}

class IRExtractFailValueFromResultExpression extends IRSimpleExpression {
    readonly rtype: IRTypeSignature;
    readonly failtype: IRTypeSignature;
    readonly etype : IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(rtype: IRTypeSignature, failtype: IRTypeSignature, etype : IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRExtractFailValueFromResultExpression);
        this.rtype = rtype;
        this.failtype = failtype;
        this.etype = etype;
        this.value = value;
    }

    static jsonEmit_IRExtractFailValueFromResultExpression(exp: IRExtractFailValueFromResultExpression): object {
        assert(false, "IRExtractFailValueFromResultExpression.jsonEmit not implemented");
    }

    static jsonParse_IRExtractFailValueFromResultExpression(obj: any): IRExtractFailValueFromResultExpression {
        assert(false, "IRExtractFailValueFromResultExpression.jsonParse not implemented");
    }
}

abstract class IRConceptRepresentationOfTypeExpression extends IRSimpleExpression {
    readonly exp: IRSimpleExpression;
    readonly exptype: IRTypeSignature;
    readonly targettype: IRTypeSignature;

    constructor(tag: IRExpressionTag, exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(tag);
        this.exp = exp;
        this.exptype = exptype;
        this.targettype = targettype;
    }

    static jsonEmit_IRConceptRepresentationOfTypeExpression(exp: IRConceptRepresentationOfTypeExpression): [string, object] {
        assert(false, "IRConceptRepresentationOfTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConceptRepresentationOfTypeExpression(obj: any): IRConceptRepresentationOfTypeExpression {
        assert(false, "IRConceptRepresentationOfTypeExpression.jsonParse not implemented");
    }
}

class IRIsConceptRepresentationOfTypeExpression extends IRConceptRepresentationOfTypeExpression {
    constructor(exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(IRExpressionTag.IRIsConceptRepresentationOfTypeExpression, exp, exptype, targettype);
    }

    static jsonEmit_IRIsConceptRepresentationOfTypeExpression(exp: IRIsConceptRepresentationOfTypeExpression): object {
        assert(false, "IRIsConceptRepresentationOfTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRIsConceptRepresentationOfTypeExpression(obj: any): IRIsConceptRepresentationOfTypeExpression {
        assert(false, "IRIsConceptRepresentationOfTypeExpression.jsonParse not implemented");
    }
}

class IRIsNotConceptRepresentationOfTypeExpression extends IRConceptRepresentationOfTypeExpression {
    constructor(exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(IRExpressionTag.IRIsNotConceptRepresentationOfTypeExpression, exp, exptype, targettype);
    }

    static jsonEmit_IRIsNotConceptRepresentationOfTypeExpression(exp: IRIsNotConceptRepresentationOfTypeExpression): object {
        assert(false, "IRIsNotConceptRepresentationOfTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRIsNotConceptRepresentationOfTypeExpression(obj: any): IRIsNotConceptRepresentationOfTypeExpression {
        assert(false, "IRIsNotConceptRepresentationOfTypeExpression.jsonParse not implemented");
    }
}

class IRIsConceptRepresentationSubtypeOfTypeExpression extends IRConceptRepresentationOfTypeExpression {
    constructor(exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(IRExpressionTag.IRIsConceptRepresentationSubtypeOfTypeExpression, exp, exptype, targettype);
    }

    static jsonEmit_IRIsConceptRepresentationSubtypeOfTypeExpression(exp: IRIsConceptRepresentationSubtypeOfTypeExpression): object {
        assert(false, "IRIsConceptRepresentationSubtypeOfTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRIsConceptRepresentationSubtypeOfTypeExpression(obj: any): IRIsConceptRepresentationSubtypeOfTypeExpression {
        assert(false, "IRIsConceptRepresentationSubtypeOfTypeExpression.jsonParse not implemented");
    }
}

class IRIsNotConceptRepresentationSubtypeOfTypeExpression extends IRConceptRepresentationOfTypeExpression {
    constructor(exp: IRSimpleExpression, exptype: IRTypeSignature, targettype: IRTypeSignature) {
        super(IRExpressionTag.IRIsNotConceptRepresentationSubtypeOfTypeExpression, exp, exptype, targettype);
    }

    static jsonEmit_IRIsNotConceptRepresentationSubtypeOfTypeExpression(exp: IRIsNotConceptRepresentationSubtypeOfTypeExpression): object {
        assert(false, "IRIsNotConceptRepresentationSubtypeOfTypeExpression.jsonEmit not implemented");
    }

    static jsonParse_IRIsNotConceptRepresentationSubtypeOfTypeExpression(obj: any): IRIsNotConceptRepresentationSubtypeOfTypeExpression {
        assert(false, "IRIsNotConceptRepresentationSubtypeOfTypeExpression.jsonParse not implemented");
    }
}

class IRStaticIsTypeSubtypeOfExpression extends IRSimpleExpression {
    readonly isnot: boolean; //true if this check is negated

    readonly exptype: IRTypeSignature;
    readonly targettype: IRTypeSignature;

    constructor(exptype: IRTypeSignature, targettype: IRTypeSignature, isnot: boolean) {
        super(IRExpressionTag.IRStaticIsTypeSubtypeOfExpression);
        this.exptype = exptype;
        this.targettype = targettype;
        this.isnot = isnot;
    }

    static jsonEmit_IRStaticIsTypeSubtypeOfExpression(exp: IRStaticIsTypeSubtypeOfExpression): object {
        assert(false, "IRStaticIsTypeSubtypeOfExpression.jsonEmit not implemented");
    }

    static jsonParse_IRStaticIsTypeSubtypeOfExpression(obj: any): IRStaticIsTypeSubtypeOfExpression {
        assert(false, "IRStaticIsTypeSubtypeOfExpression.jsonParse not implemented");
    }
}

class IRBoxEntityToConceptRepresentationExpression extends IRSimpleExpression {
    readonly totype: IRTypeSignature;
    readonly fromtype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(totype: IRTypeSignature, fromtype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRBoxEntityToConceptRepresentationExpression);
        this.totype = totype;
        this.fromtype = fromtype;
        this.value = value;
    }

    static jsonEmit_IRBoxEntityToConceptRepresentationExpression(exp: IRBoxEntityToConceptRepresentationExpression): object {
        assert(false, "IRBoxEntityToConceptRepresentationExpression.jsonEmit not implemented");
    }

    static jsonParse_IRBoxEntityToConceptRepresentationExpression(obj: any): IRBoxEntityToConceptRepresentationExpression {
        assert(false, "IRBoxEntityToConceptRepresentationExpression.jsonParse not implemented");
    }
}

class IRUnboxEntityFromConceptRepresentationExpression extends IRSimpleExpression {
    readonly fromtype: IRTypeSignature;
    readonly totype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(fromtype: IRTypeSignature, totype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRUnboxEntityFromConceptRepresentationExpression);
        this.fromtype = fromtype;
        this.totype = totype;
        this.value = value;
    }
    
    static jsonEmit_IRUnboxEntityFromConceptRepresentationExpression(exp: IRUnboxEntityFromConceptRepresentationExpression): object {
        assert(false, "IRUnboxEntityFromConceptRepresentationExpression.jsonEmit not implemented");
    }

    static jsonParse_IRUnboxEntityFromConceptRepresentationExpression(obj: any): IRUnboxEntityFromConceptRepresentationExpression {
        assert(false, "IRUnboxEntityFromConceptRepresentationExpression.jsonParse not implemented");
    }
}

class IRConvertConceptRepresentationExpression extends IRSimpleExpression {
    readonly fromtype: IRTypeSignature;
    readonly totype: IRTypeSignature;
    readonly value: IRSimpleExpression;

    constructor(fromtype: IRTypeSignature, totype: IRTypeSignature, value: IRSimpleExpression) {
        super(IRExpressionTag.IRConvertConceptRepresentationExpression);
        this.fromtype = fromtype;
        this.totype = totype;
        this.value = value;
    }

    static jsonEmit_IRConvertConceptRepresentationExpression(exp: IRConvertConceptRepresentationExpression): object {
        assert(false, "IRConvertConceptRepresentationExpression.jsonEmit not implemented");
    }

    static jsonParse_IRConvertConceptRepresentationExpression(obj: any): IRConvertConceptRepresentationExpression {
        assert(false, "IRConvertConceptRepresentationExpression.jsonParse not implemented");
    }
}

////////////////////////////////////////
//Basic Line statements

class IRNopStatement extends IRAtomicStatement {
    constructor() {
        super(IRStatementTag.IRNopStatement);
    }

    override isSimpleStatement(): boolean {
        return true;
    }

    static jsonEmit_IRNopStatement(exp: IRNopStatement): object {
        return {};
    }

    static jsonParse_IRNopStatement(obj: any): IRNopStatement {
        return new IRNopStatement();
    }
}

class IRTempAssignExpressionStatement extends IRTempAssignStatement {
    readonly rhs: IRExpression;

    constructor(tname: number, ttype: IRTypeSignature, rhs: IRExpression) {
        super(IRStatementTag.IRTempAssignExpressionStatement, tname, ttype);
        this.rhs = rhs;
    }

    override isSimpleStatement(): boolean {
        return this.rhs.isSimpleExpression();
    }

    static jsonEmit_IRTempAssignExpressionStatement(exp: IRTempAssignExpressionStatement): object {
        const nval = IRTempAssignStatement.jsonEmitMeta_IRTempAssignStatement(exp);

        return {
            ...nval,
            rhs: IRExpression.jsonEmit_IRExpression(exp.rhs)
        };
    }

    static jsonParse_IRTempAssignExpressionStatement(obj: any): IRTempAssignExpressionStatement {
        const nval = IRTempAssignStatement.jsonParseMeta_IRTempAssignStatement(obj);
        const rhs = IRExpression.jsonParse_IRExpression(obj.rhs);

        return new IRTempAssignExpressionStatement(...nval, rhs);
    }
}

class IRTempAssignStdInvokeStatement extends IRTempAssignStatement {
    readonly rhs: IRInvokeSimpleExpression;

    constructor(tname: number, ttype: IRTypeSignature, rhs: IRInvokeSimpleExpression) {
        super(IRStatementTag.IRTempAssignStdInvokeStatement, tname, ttype);
        this.rhs = rhs;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRTempAssignStdInvokeStatement(exp: IRTempAssignStdInvokeStatement): object {
        const nval = IRTempAssignStatement.jsonEmitMeta_IRTempAssignStatement(exp);

        return {
            ...nval,
            rhs: IRExpression.jsonEmit_IRExpression(exp.rhs)
        };
    }

    static jsonParse_IRTempAssignStdInvokeStatement(obj: any): IRTempAssignStdInvokeStatement {
        const nval = IRTempAssignStatement.jsonParseMeta_IRTempAssignStatement(obj);
        const rhs = IRInvokeSimpleExpression.jsonParse_IRInvokeSimpleExpression(obj.rhs);

        return new IRTempAssignStdInvokeStatement(...nval, rhs);
    }
}

//We definitely need to have the var type include the ref/out/intout.. placeholder info AND may need to check error results on this in smt
class IRTempAssignRefInvokeStatement extends IRTempAssignStatement {
    readonly ivar: string; //the implicit variable to assign the returned ref/out/out?/inout parameter
    readonly ivartype: IRTypeSignature;
    readonly passkind : IRImplicitInvokeArgPassKind;
    readonly rhs: IRInvokeImplicitsExpression;

    constructor(tname: number, ttype: IRTypeSignature, ivar: string, ivartype: IRTypeSignature, passkind: IRImplicitInvokeArgPassKind, rhs: IRInvokeImplicitsExpression) {
        super(IRStatementTag.IRTempAssignRefInvokeStatement, tname, ttype);
        this.ivar = ivar;
        this.ivartype = ivartype;
        this.passkind = passkind;
        this.rhs = rhs;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRTempAssignRefInvokeStatement(exp: IRTempAssignRefInvokeStatement): object {
        const nval = IRTempAssignStatement.jsonEmitMeta_IRTempAssignStatement(exp);

        return {
            ...nval,
            ivar: exp.ivar,
            ivartype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.ivartype),
            passkind: `Assembly::${exp.passkind}`,
            rhs: IRInvokeImplicitsExpression.jsonEmit_IRInvokeImplicitsExpression(exp.rhs)
        };
    }

    static jsonParse_IRTempAssignRefInvokeStatement(obj: any): IRTempAssignRefInvokeStatement {
        const nval = IRTempAssignStatement.jsonParseMeta_IRTempAssignStatement(obj);
        const ivar = obj.ivar;
        const ivartype = IRTypeSignature.jsonParse_IRTypeSignature(obj.ivartype);
        const passkind = obj.passkind.replace("Assembly::", "");
        const rhs = IRInvokeImplicitsExpression.jsonParse_IRInvokeImplicitsExpression(obj.rhs);

        return new IRTempAssignRefInvokeStatement(...nval, ivar, ivartype, passkind, rhs);
    }
}

class IRTempAssignDirectConstructorStatement extends IRTempAssignStatement {
    readonly rhs: IRConstructExpression;

    constructor(tname: number, ttype: IRTypeSignature, rhs: IRConstructExpression) {
        super(IRStatementTag.IRTempAssignDirectConstructorStatement, tname, ttype);
        this.rhs = rhs;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRTempAssignDirectConstructorStatement(exp: IRTempAssignDirectConstructorStatement): object {
        const nval = IRTempAssignStatement.jsonEmitMeta_IRTempAssignStatement(exp);

        return {
            ...nval,
            rhs: IRConstructExpression.jsonEmit_IRConstructExpression(exp.rhs)
        };
    }

    static jsonParse_IRTempAssignDirectConstructorStatement(obj: any): IRTempAssignDirectConstructorStatement {
        const nval = IRTempAssignStatement.jsonParseMeta_IRTempAssignStatement(obj);
        const rhs = IRConstructExpression.jsonParse_IRConstructExpression(obj.rhs);

        return new IRTempAssignDirectConstructorStatement(...nval, rhs);
    }
}

class IRVariableDeclarationStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;

    constructor(vname: string, vtype: IRTypeSignature) {
        super(IRStatementTag.IRVariableDeclarationStatement);
        this.vname = vname;
        this.vtype = vtype;
    }

    override isSimpleStatement(): boolean {
        return true;
    }

    static jsonEmit_IRVariableDeclarationStatement(exp: IRVariableDeclarationStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype)
        };
    }

    static jsonParse_IRVariableDeclarationStatement(obj: any): IRVariableDeclarationStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        return new IRVariableDeclarationStatement(obj.vname, vtype);
    }
}

class IRVariableInitializationStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly initexp: IRSimpleExpression;
    readonly isconst: boolean;

    constructor(vname: string, vtype: IRTypeSignature, initexp: IRSimpleExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return this.initexp.isSimpleExpression();
    }

    static jsonEmit_IRVariableInitializationStatement(exp: IRVariableInitializationStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            initexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.initexp),
            isconst: exp.isconst
        };
    }

    static jsonParse_IRVariableInitializationStatement(obj: any): IRVariableInitializationStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const initexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.initexp);
        return new IRVariableInitializationStatement(obj.vname, vtype, initexp, obj.isconst);
    }
}

class IRVariableInitializationDirectInvokeStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly initexp: IRInvokeDirectExpression;
    readonly isconst: boolean;

    constructor(vname: string, vtype: IRTypeSignature, initexp: IRInvokeDirectExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationDirectInvokeStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVariableInitializationDirectInvokeStatement(exp: IRVariableInitializationDirectInvokeStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            initexp: IRInvokeDirectExpression.jsonEmit_IRInvokeDirectExpression(exp.initexp),
            isconst: exp.isconst
        };
    }

    static jsonParse_IRVariableInitializationDirectInvokeStatement(obj: any): IRVariableInitializationDirectInvokeStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const initexp = IRInvokeDirectExpression.jsonParse_IRInvokeDirectExpression(obj.initexp);
        return new IRVariableInitializationDirectInvokeStatement(obj.vname, vtype, initexp, obj.isconst);
    }
}

class IRVariableInitializationDirectInvokeWithImplicitStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly initexp: IRInvokeImplicitsExpression;
    readonly isconst: boolean;

    constructor(vname: string, vtype: IRTypeSignature, initexp: IRInvokeImplicitsExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationDirectInvokeWithImplicitStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVariableInitializationDirectInvokeWithImplicitStatement(exp: IRVariableInitializationDirectInvokeWithImplicitStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            initexp: IRInvokeImplicitsExpression.jsonEmit_IRInvokeImplicitsExpression(exp.initexp),
            isconst: exp.isconst
        };
    }

    static jsonParse_IRVariableInitializationDirectInvokeWithImplicitStatement(obj: any): IRVariableInitializationDirectInvokeWithImplicitStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const initexp = IRInvokeImplicitsExpression.jsonParse_IRInvokeImplicitsExpression(obj.initexp);
        return new IRVariableInitializationDirectInvokeWithImplicitStatement(obj.vname, vtype, initexp, obj.isconst);
    }
}

class IRVariableInitializationDirectConstructorStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly initexp: IRConstructExpression;
    readonly isconst: boolean;

    constructor(vname: string, vtype: IRTypeSignature, initexp: IRConstructExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationDirectConstructorStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVariableInitializationDirectConstructorStatement(exp: IRVariableInitializationDirectConstructorStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            initexp: IRConstructExpression.jsonEmit_IRConstructExpression(exp.initexp),
            isconst: exp.isconst
        };
    }

    static jsonParse_IRVariableInitializationDirectConstructorStatement(obj: any): IRVariableInitializationDirectConstructorStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const initexp = IRConstructExpression.jsonParse_IRConstructExpression(obj.initexp);
        return new IRVariableInitializationDirectConstructorStatement(obj.vname, vtype, initexp, obj.isconst);
    }
}

class IRVariableInitializationDirectConstructorWithBoxStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly fromtype: IRTypeSignature;
    readonly initexp: IRConstructExpression;
    readonly isconst: boolean;

    constructor(vname: string, vtype: IRTypeSignature, fromtype: IRTypeSignature, initexp: IRConstructExpression, isconst: boolean) {
        super(IRStatementTag.IRVariableInitializationDirectConstructorWithBoxStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.fromtype = fromtype;
        this.initexp = initexp;
        this.isconst = isconst;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVariableInitializationDirectConstructorWithBoxStatement(exp: IRVariableInitializationDirectConstructorWithBoxStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            fromtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.fromtype),
            initexp: IRConstructExpression.jsonEmit_IRConstructExpression(exp.initexp),
            isconst: exp.isconst
        };
    }

    static jsonParse_IRVariableInitializationDirectConstructorWithBoxStatement(obj: any): IRVariableInitializationDirectConstructorWithBoxStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const fromtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.fromtype);
        const initexp = IRConstructExpression.jsonParse_IRConstructExpression(obj.initexp);
        return new IRVariableInitializationDirectConstructorWithBoxStatement(obj.vname, vtype, fromtype, initexp, obj.isconst);
    }
}

class IRVariableAssignmentStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aexp: IRSimpleExpression;

    constructor(vname: string, vtype: IRTypeSignature, aexp: IRSimpleExpression) {
        super(IRStatementTag.IRVariableAssignmentStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return this.aexp.isSimpleExpression();
    }

    static jsonEmit_IRVariableAssignmentStatement(exp: IRVariableAssignmentStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            aexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.aexp)
        };
    }

    static jsonParse_IRVariableAssignmentStatement(obj: any): IRVariableAssignmentStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const aexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.aexp);
        return new IRVariableAssignmentStatement(obj.vname, vtype, aexp);
    }
}

class IRVariableAssignmentDirectInvokeStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aexp: IRInvokeDirectExpression;

    constructor(vname: string, vtype: IRTypeSignature, aexp: IRInvokeDirectExpression) {
        super(IRStatementTag.IRVariableAssignmentDirectInvokeStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVariableAssignmentDirectInvokeStatement(exp: IRVariableAssignmentDirectInvokeStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            aexp: IRInvokeDirectExpression.jsonEmit_IRInvokeDirectExpression(exp.aexp)
        };
    }

    static jsonParse_IRVariableAssignmentDirectInvokeStatement(obj: any): IRVariableAssignmentDirectInvokeStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const aexp = IRInvokeDirectExpression.jsonParse_IRInvokeDirectExpression(obj.aexp);
        return new IRVariableAssignmentDirectInvokeStatement(obj.vname, vtype, aexp);
    }
}

class IRVariableAssignmentDirectInvokeWithImplicitStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aexp: IRInvokeImplicitsExpression;

    constructor(vname: string, vtype: IRTypeSignature, aexp: IRInvokeImplicitsExpression) {
        super(IRStatementTag.IRVariableAssignmentDirectInvokeWithImplicitStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVariableAssignmentDirectInvokeWithImplicitStatement(exp: IRVariableAssignmentDirectInvokeWithImplicitStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            aexp: IRInvokeImplicitsExpression.jsonEmit_IRInvokeImplicitsExpression(exp.aexp)
        };
    }

    static jsonParse_IRVariableAssignmentDirectInvokeWithImplicitStatement(obj: any): IRVariableAssignmentDirectInvokeWithImplicitStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const aexp = IRInvokeImplicitsExpression.jsonParse_IRInvokeImplicitsExpression(obj.aexp);
        return new IRVariableAssignmentDirectInvokeWithImplicitStatement(obj.vname, vtype, aexp);
    }
}

class IRVariableAssignmentDirectConstructorStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aexp: IRConstructExpression;

    constructor(vname: string, vtype: IRTypeSignature, aexp: IRConstructExpression) {
        super(IRStatementTag.IRVariableAssignmentDirectConstructorStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVariableAssignmentDirectConstructorStatement(exp: IRVariableAssignmentDirectConstructorStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            aexp: IRConstructExpression.jsonEmit_IRConstructExpression(exp.aexp)
        };
    }

    static jsonParse_IRVariableAssignmentDirectConstructorStatement(obj: any): IRVariableAssignmentDirectConstructorStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const aexp = IRConstructExpression.jsonParse_IRConstructExpression(obj.aexp);
        return new IRVariableAssignmentDirectConstructorStatement(obj.vname, vtype, aexp);
    }
}

class IRVariableAssignmentDirectConstructorWithBoxStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly fromtype: IRTypeSignature;
    readonly aexp: IRConstructExpression;

    constructor(vname: string, vtype: IRTypeSignature, fromtype: IRTypeSignature, aexp: IRConstructExpression) {
        super(IRStatementTag.IRVariableAssignmentDirectConstructorWithBoxStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.fromtype = fromtype;
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVariableAssignmentDirectConstructorWithBoxStatement(exp: IRVariableAssignmentDirectConstructorWithBoxStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            fromtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.fromtype),
            aexp: IRConstructExpression.jsonEmit_IRConstructExpression(exp.aexp)
        };
    }

    static jsonParse_IRVariableAssignmentDirectConstructorWithBoxStatement(obj: any): IRVariableAssignmentDirectConstructorWithBoxStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const fromtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.fromtype);
        const aexp = IRConstructExpression.jsonParse_IRConstructExpression(obj.aexp);
        return new IRVariableAssignmentDirectConstructorWithBoxStatement(obj.vname, vtype, fromtype, aexp);
    }
}

class IRUpdateLocalDirectStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature
    readonly aargs: IRSimpleExpression[];

    constructor(vname: string, vtype: IRTypeSignature, aargs: IRSimpleExpression[]) {
        super(IRStatementTag.IRUpdateLocalDirectStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aargs = aargs;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRUpdateLocalDirectStatement(exp: IRUpdateLocalDirectStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            aargs: exp.aargs.map(IRSimpleExpression.jsonEmit_IRSimpleExpression)
        };
    }

    static jsonParse_IRUpdateLocalDirectStatement(obj: any): IRUpdateLocalDirectStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const aargs = obj.aargs.map(IRSimpleExpression.jsonParse_IRSimpleExpression);
        return new IRUpdateLocalDirectStatement(obj.vname, vtype, aargs);
    }
}

class IRUpdateParamDirectStatement extends IRAtomicStatement {
    readonly vname: string;
    readonly vtype: IRTypeSignature;
    readonly aargs: IRSimpleExpression[];

    constructor(vname: string, vtype: IRTypeSignature, aargs: IRSimpleExpression[]) {
        super(IRStatementTag.IRUpdateParamDirectStatement);
        this.vname = vname;
        this.vtype = vtype;
        this.aargs = aargs;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRUpdateParamDirectStatement(exp: IRUpdateParamDirectStatement): object {
        return {
            vname: exp.vname,
            vtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.vtype),
            aargs: exp.aargs.map(IRSimpleExpression.jsonEmit_IRSimpleExpression)
        };
    }

    static jsonParse_IRUpdateParamDirectStatement(obj: any): IRUpdateParamDirectStatement {
        const vtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.vtype);
        const aargs = obj.aargs.map(IRSimpleExpression.jsonParse_IRSimpleExpression);
        return new IRUpdateParamDirectStatement(obj.vname, vtype, aargs);
    }
}

//
//TODO: lots more statement types here
//

class IRReturnVoidSimpleStatement extends IRReturnSimpleStatement {
    constructor() {
        super(IRStatementTag.IRReturnVoidSimpleStatement);
    }

    override isSimpleStatement(): boolean {
        return true;
    }

    static jsonEmit_IRReturnVoidSimpleStatement(exp: IRReturnVoidSimpleStatement): object {
        return {};
    }

    static jsonParse_IRReturnVoidSimpleStatement(obj: any): IRReturnVoidSimpleStatement {
        return new IRReturnVoidSimpleStatement();
    }
}

class IRReturnValueSimpleStatement extends IRReturnSimpleStatement {
    readonly retexp: IRSimpleExpression;

    constructor(retexp: IRSimpleExpression) {
        super(IRStatementTag.IRReturnValueSimpleStatement);
        this.retexp = retexp;
    }

    override isSimpleStatement(): boolean {
        return this.retexp.isSimpleExpression();
    }

    static jsonEmit_IRReturnValueSimpleStatement(exp: IRReturnValueSimpleStatement): object {
        return {
            retexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.retexp)
        };
    }

    static jsonParse_IRReturnValueSimpleStatement(obj: any): IRReturnValueSimpleStatement {
        const retexp = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.retexp);
        return new IRReturnValueSimpleStatement(retexp);
    }
}

class IRReturnDirectInvokeStatement extends IRReturnSimpleStatement {
    readonly retexp: IRInvokeDirectExpression;

    constructor(retexp: IRInvokeDirectExpression) {
        super(IRStatementTag.IRReturnDirectInvokeStatement);
        this.retexp = retexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRReturnDirectInvokeStatement(exp: IRReturnDirectInvokeStatement): object {
        return {
            retexp: IRInvokeDirectExpression.jsonEmit_IRInvokeDirectExpression(exp.retexp)
        };
    }

    static jsonParse_IRReturnDirectInvokeStatement(obj: any): IRReturnDirectInvokeStatement {
        const retexp = IRInvokeDirectExpression.jsonParse_IRInvokeDirectExpression(obj.retexp);
        return new IRReturnDirectInvokeStatement(retexp);
    }
}

class IRReturnDirectConstructStatement extends IRReturnSimpleStatement {
    readonly retexp: IRConstructExpression;

    constructor(retexp: IRConstructExpression) {
        super(IRStatementTag.IRReturnDirectConstructStatement);
        this.retexp = retexp;
    }
    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRReturnDirectConstructStatement(exp: IRReturnDirectConstructStatement): object {
        return {
            retexp: IRConstructExpression.jsonEmit_IRConstructExpression(exp.retexp)
        };
    }

    static jsonParse_IRReturnDirectConstructStatement(obj: any): IRReturnDirectConstructStatement {
        const retexp = IRConstructExpression.jsonParse_IRConstructExpression(obj.retexp);
        return new IRReturnDirectConstructStatement(retexp);
    }
}

class IRReturnDirectConstructWithBoxStatement extends IRReturnSimpleStatement {
    readonly retexp: IRConstructExpression;
    readonly fromtype: IRTypeSignature;
    readonly totype: IRTypeSignature;

    constructor(retexp: IRConstructExpression, fromtype: IRTypeSignature, totype: IRTypeSignature) {
        super(IRStatementTag.IRReturnDirectConstructWithBoxStatement);
        this.retexp = retexp;
        this.fromtype = fromtype;
        this.totype = totype;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRReturnDirectConstructWithBoxStatement(exp: IRReturnDirectConstructWithBoxStatement): object {
        return {
            retexp: IRConstructExpression.jsonEmit_IRConstructExpression(exp.retexp),
            fromtype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.fromtype),
            totype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.totype)
        };
    }

    static jsonParse_IRReturnDirectConstructWithBoxStatement(obj: any): IRReturnDirectConstructWithBoxStatement {
        const retexp = IRConstructExpression.jsonParse_IRConstructExpression(obj.retexp);
        const fromtype = IRTypeSignature.jsonParse_IRTypeSignature(obj.fromtype);
        const totype = IRTypeSignature.jsonParse_IRTypeSignature(obj.totype);
        return new IRReturnDirectConstructWithBoxStatement(retexp, fromtype, totype);
    }
}

class IRVoidInvokeStatement extends IRAtomicStatement {
    readonly aexp: IRInvokeImplicitsExpression;

    constructor(aexp: IRInvokeImplicitsExpression) {
        super(IRStatementTag.IRVoidInvokeStatement);
        this.aexp = aexp;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRVoidInvokeStatement(exp: IRVoidInvokeStatement): object {
        return {
            aexp: IRInvokeImplicitsExpression.jsonEmit_IRInvokeImplicitsExpression(exp.aexp)
        };
    }

    static jsonParse_IRVoidInvokeStatement(obj: any): IRVoidInvokeStatement {
        const aexp = IRInvokeImplicitsExpression.jsonParse_IRInvokeImplicitsExpression(obj.aexp);
        return new IRVoidInvokeStatement(aexp);
    }
}

class IRChkLogicImpliesShortCircuitStatement extends IRStatement {
    readonly tvar: number; //the temp variable to hold the result
    readonly lhs: IRSimpleExpression;
    readonly rstmts: IRStatement[];
    readonly rexp: IRSimpleExpression;

    constructor(tvar: number, lhs: IRSimpleExpression, rstmts: IRStatement[], rexp: IRSimpleExpression) {
        super(IRStatementTag.IRChkLogicImpliesShortCircuitStatement);
        this.tvar = tvar;
        this.lhs = lhs;
        this.rstmts = rstmts;
        this.rexp = rexp;
    }

    override isSimpleStatement(): boolean {
        return this.lhs.isSimpleExpression() && this.rstmts.every(s => s.isSimpleStatement()) && this.rexp.isSimpleExpression();
    }

    static jsonEmit_IRChkLogicImpliesShortCircuitStatement(exp: IRChkLogicImpliesShortCircuitStatement): object {
        assert(false, "Not implemented -- jsonEmit_IRChkLogicImpliesShortCircuitStatement");
    }

    static jsonParse_IRChkLogicImpliesShortCircuitStatement(obj: any): IRChkLogicImpliesShortCircuitStatement {
        assert(false, "Not implemented -- jsonParse_IRChkLogicImpliesShortCircuitStatement");
    }
}

class IRLogicConditionalStatement extends IRStatement {
    readonly tvar: number; //the temp variable to hold the result
    readonly ttype: IRTypeSignature;
    readonly condition: IRSimpleExpression;
    readonly truestmt: IRStatement[];
    readonly trueexp: IRSimpleExpression;
    readonly falsestmt: IRStatement[];
    readonly falseexp: IRSimpleExpression;

    constructor(tvar: number, ttype: IRTypeSignature, condition: IRSimpleExpression, truestmt: IRStatement[], trueexp: IRSimpleExpression, falsestmt: IRStatement[], falseexp: IRSimpleExpression) {
        super(IRStatementTag.IRLogicConditionalStatement);
        this.tvar = tvar;
        this.ttype = ttype;
        this.condition = condition;
        this.truestmt = truestmt;
        this.trueexp = trueexp;
        this.falsestmt = falsestmt;
        this.falseexp = falseexp;
    }

    override isSimpleStatement(): boolean {
        return this.condition.isSimpleExpression() && this.truestmt.every(s => s.isSimpleStatement()) && this.trueexp.isSimpleExpression() && this.falsestmt.every(s => s.isSimpleStatement()) && this.falseexp.isSimpleExpression();
    }

    static jsonEmit_IRLogicConditionalStatement(exp: IRLogicConditionalStatement): object {
        assert(false, "Not implemented -- jsonEmit_IRLogicConditionalStatement");
    }

    static jsonParse_IRLogicConditionalStatement(obj: any): IRLogicConditionalStatement {
        assert(false, "Not implemented -- jsonParse_IRLogicConditionalStatement");
    }
}

class IRSimpleIfStatement extends IRStatement {
    readonly cond: IRSimpleExpression;
    readonly tblock: IRBlockStatement;

    constructor(cond: IRSimpleExpression, tblock: IRBlockStatement) {
        super(IRStatementTag.IRSimpleIfStatement);
        this.cond = cond;
        this.tblock = tblock;
    }

    override isSimpleStatement(): boolean {
        return this.cond.isSimpleExpression() && this.tblock.isSimpleStatement();
    }

    static jsonEmit_IRSimpleIfStatement(exp: IRSimpleIfStatement): object {
        return {
            cond: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.cond),
            tblock: IRBlockStatement.jsonEmit_IRBlockStatement(exp.tblock)
        };
    }

    static jsonParse_IRSimpleIfStatement(obj: any): IRSimpleIfStatement {
        const cond = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.cond);
        const tblock = IRBlockStatement.jsonParse_IRBlockStatement(obj.tblock);
        return new IRSimpleIfStatement(cond, tblock);
    }
}

class IRSimpleIfElseStatement extends IRStatement {
    readonly cond: IRSimpleExpression;
    readonly tblock: IRBlockStatement;
    readonly eblock: IRBlockStatement;

    constructor(cond: IRSimpleExpression, tblock: IRBlockStatement, eblock: IRBlockStatement) {
        super(IRStatementTag.IRSimpleIfElseStatement);
        this.cond = cond;
        this.tblock = tblock;
        this.eblock = eblock;
    }

    override isTerminalStatement(): boolean { 
        return this.tblock.isTerminalStatement() && this.eblock.isTerminalStatement(); 
    }

    override isSimpleStatement(): boolean {
        return this.cond.isSimpleExpression() && this.tblock.isSimpleStatement() && this.eblock.isSimpleStatement();
    }

    static jsonEmit_IRSimpleIfElseStatement(exp: IRSimpleIfElseStatement): object {
        return {
            cond: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.cond),
            tblock: IRBlockStatement.jsonEmit_IRBlockStatement(exp.tblock),
            eblock: IRBlockStatement.jsonEmit_IRBlockStatement(exp.eblock)
        };
    }

    static jsonParse_IRSimpleIfElseStatement(obj: any): IRSimpleIfElseStatement {
        const cond = IRSimpleExpression.jsonParse_IRSimpleExpression(obj.cond);
        const tblock = IRBlockStatement.jsonParse_IRBlockStatement(obj.tblock);
        const eblock = IRBlockStatement.jsonParse_IRBlockStatement(obj.eblock);
        return new IRSimpleIfElseStatement(cond, tblock, eblock);
    }
}

class IRMatchExactStatement extends IRStatement {
    readonly sval: IRImmediateExpression;
    readonly svaltype: IRTypeSignature;
    readonly bindervar: string;
    readonly matchflow: {mtype: IRTypeSignature | undefined, value: IRBlockStatement}[];
    implicitFinalType: IRTypeSignature;

    constructor(sval: IRImmediateExpression, svaltype: IRTypeSignature, bindername: string, flow: {mtype: IRTypeSignature | undefined, value: IRBlockStatement}[], implicitFinalType: IRTypeSignature) {
        super(IRStatementTag.IRMatchExactStatement);
        this.sval = sval;
        this.svaltype = svaltype;
        this.bindervar = bindername;
        this.matchflow = flow;
        this.implicitFinalType = implicitFinalType;
    }

    override isTerminalStatement(): boolean { 
        return this.matchflow.every(f => f.value.isTerminalStatement()); 
    }

    override isSimpleStatement(): boolean {
        return this.sval.isSimpleExpression() && this.matchflow.every(f => f.value.isSimpleStatement());
    }

    static jsonEmit_IRMatchExactStatement(exp: IRMatchExactStatement): object {
        return {
            sval: IRImmediateExpression.jsonEmit_IRImmediateExpression(exp.sval),
            svaltype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.svaltype),
            bindervar: exp.bindervar,
            matchflow: exp.matchflow.map(f => ({mtype: f.mtype ? IRTypeSignature.jsonEmit_IRTypeSignature(f.mtype) : undefined, value: IRBlockStatement.jsonEmit_IRBlockStatement(f.value)})),
            implicitFinalType: IRTypeSignature.jsonEmit_IRTypeSignature(exp.implicitFinalType)
        };
    }

    static jsonParse_IRMatchExactStatement(obj: any): IRMatchExactStatement {
        const sval = IRImmediateExpression.jsonParse_IRImmediateExpression(obj.sval);
        const svaltype = IRTypeSignature.jsonParse_IRTypeSignature(obj.svaltype);
        const bindervar = obj.bindervar;
        const matchflow = obj.matchflow.map((f: any) => ({mtype: f.mtype ? IRTypeSignature.jsonParse_IRTypeSignature(f.mtype) : undefined, value: IRBlockStatement.jsonParse_IRBlockStatement(f.value)}));
        const implicitFinalType = IRTypeSignature.jsonParse_IRTypeSignature(obj.implicitFinalType);
        return new IRMatchExactStatement(sval, svaltype, bindervar, matchflow, implicitFinalType);
    }
}

class IRMatchGeneralStatement extends IRStatement {
    readonly sval: IRImmediateExpression;
    readonly svaltype: IRTypeSignature;
    readonly bindervar: string;
    readonly matchflow: {mtype: IRTypeSignature | undefined, value: IRBlockStatement}[];
    implicitFinalType: IRTypeSignature;

    constructor(sval: IRImmediateExpression, svaltype: IRTypeSignature, bindername: string, flow: {mtype: IRTypeSignature | undefined, value: IRBlockStatement}[], implicitFinalType: IRTypeSignature) {
        super(IRStatementTag.IRMatchGeneralStatement);
        this.sval = sval;
        this.svaltype = svaltype;
        this.bindervar = bindername;
        this.matchflow = flow;
        this.implicitFinalType = implicitFinalType;
    }

    override isTerminalStatement(): boolean { 
        return this.matchflow.every(f => f.value.isTerminalStatement()); 
    }

    override isSimpleStatement(): boolean {
        return this.sval.isSimpleExpression() && this.matchflow.every(f => f.value.isSimpleStatement());
    }

    static jsonEmit_IRMatchGeneralStatement(exp: IRMatchGeneralStatement): object {
        return {
            sval: IRImmediateExpression.jsonEmit_IRImmediateExpression(exp.sval),
            svaltype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.svaltype),
            bindervar: exp.bindervar,
            matchflow: exp.matchflow.map(f => ({mtype: f.mtype ? IRTypeSignature.jsonEmit_IRTypeSignature(f.mtype) : undefined, value: IRBlockStatement.jsonEmit_IRBlockStatement(f.value)})),
            implicitFinalType: IRTypeSignature.jsonEmit_IRTypeSignature(exp.implicitFinalType)
        };
    }

    static jsonParse_IRMatchGeneralStatement(obj: any): IRMatchGeneralStatement {
        const sval = IRImmediateExpression.jsonParse_IRImmediateExpression(obj.sval);
        const svaltype = IRTypeSignature.jsonParse_IRTypeSignature(obj.svaltype);
        const bindervar = obj.bindervar;
        const matchflow = obj.matchflow.map((f: any) => ({mtype: f.mtype ? IRTypeSignature.jsonParse_IRTypeSignature(f.mtype) : undefined, value: IRBlockStatement.jsonParse_IRBlockStatement(f.value)}));
        const implicitFinalType = IRTypeSignature.jsonParse_IRTypeSignature(obj.implicitFinalType);
        return new IRMatchGeneralStatement(sval, svaltype, bindervar, matchflow, implicitFinalType);
    }
}

class IRErrorAdditionBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(IRStatementTag.IRErrorAdditionBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }

    static jsonEmit_IRErrorAdditionBoundsCheckStatement(exp: IRErrorAdditionBoundsCheckStatement): object {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);
        const bval = IRErrorBinArithCheckStatement.jsonEmitMeta_IRErrorBinArithCheckStatement(exp);

        return {
            ...nval,
            ...bval
        };
    }

    static jsonParse_IRErrorAdditionBoundsCheckStatement(obj: any): IRErrorAdditionBoundsCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);
        const bval = IRErrorBinArithCheckStatement.jsonParseMeta_IRErrorBinArithCheckStatement(obj);

        return new IRErrorAdditionBoundsCheckStatement(nval[0], nval[1], nval[3], ...bval);
    }
}

class IRErrorSubtractionBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(IRStatementTag.IRErrorSubtractionBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }

    static jsonEmit_IRErrorSubtractionBoundsCheckStatement(exp: IRErrorSubtractionBoundsCheckStatement): object {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);
        const bval = IRErrorBinArithCheckStatement.jsonEmitMeta_IRErrorBinArithCheckStatement(exp);

        return {
            ...nval,
            ...bval
        };
    }

    static jsonParse_IRErrorSubtractionBoundsCheckStatement(obj: any): IRErrorSubtractionBoundsCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);
        const bval = IRErrorBinArithCheckStatement.jsonParseMeta_IRErrorBinArithCheckStatement(obj);

        return new IRErrorSubtractionBoundsCheckStatement(nval[0], nval[1], nval[3], ...bval);
    }
}

class IRErrorMultiplicationBoundsCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(IRStatementTag.IRErrorMultiplicationBoundsCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }

    static jsonEmit_IRErrorMultiplicationBoundsCheckStatement(exp: IRErrorMultiplicationBoundsCheckStatement): object {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);
        const bval = IRErrorBinArithCheckStatement.jsonEmitMeta_IRErrorBinArithCheckStatement(exp);

        return {
            ...nval,
            ...bval
        };
    }

    static jsonParse_IRErrorMultiplicationBoundsCheckStatement(obj: any): IRErrorMultiplicationBoundsCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);
        const bval = IRErrorBinArithCheckStatement.jsonParseMeta_IRErrorBinArithCheckStatement(obj);

        return new IRErrorMultiplicationBoundsCheckStatement(nval[0], nval[1], nval[3], ...bval);
    }
}

class IRErrorDivisionByZeroCheckStatement extends IRErrorBinArithCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number, left: IRImmediateExpression, right: IRImmediateExpression, optypechk: "Nat" | "Int" | "ChkNat" | "ChkInt" | "Float") {
        super(IRStatementTag.IRErrorDivisionByZeroCheckStatement, file, sinfo, undefined, checkID, left, right, optypechk);
    }

    static jsonEmit_IRErrorDivisionByZeroCheckStatement(exp: IRErrorDivisionByZeroCheckStatement): object {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);
        const bval = IRErrorBinArithCheckStatement.jsonEmitMeta_IRErrorBinArithCheckStatement(exp);

        return {
            ...nval,
            ...bval
        };
    }

    static jsonParse_IRErrorDivisionByZeroCheckStatement(obj: any): IRErrorDivisionByZeroCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);
        const bval = IRErrorBinArithCheckStatement.jsonParseMeta_IRErrorBinArithCheckStatement(obj);

        return new IRErrorDivisionByZeroCheckStatement(nval[0], nval[1], nval[3], ...bval);
    }
}

class IRErrorTypeAssertionCheckStatement extends IRErrorCheckStatement {
    readonly typeok: IRSimpleExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, typeok: IRSimpleExpression) {
        super(IRStatementTag.IRErrorTypeAssertionCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.typeok = typeok;
    }

    static jsonEmit_IRErrorTypeAssertionCheckStatement(exp: IRErrorTypeAssertionCheckStatement): object {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval,
            typeok: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.typeok)
        };
    }

    static jsonParse_IRErrorTypeAssertionCheckStatement(obj: any): IRErrorTypeAssertionCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IRErrorTypeAssertionCheckStatement(nval[0], nval[1], nval[2], nval[3], IRSimpleExpression.jsonParse_IRSimpleExpression(obj.typeok));
    }
}

class IRErrorExhaustiveStatement extends IRErrorCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, checkID: number) {
        super(IRStatementTag.IRErrorExhaustiveStatement, file, sinfo, undefined, checkID);
    }

    override isTerminalStatement(): boolean { return true; }

    static jsonEmit_IRErrorExhaustiveStatement(exp: IRErrorExhaustiveStatement): object {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval
        };
    }

    static jsonParse_IRErrorExhaustiveStatement(obj: any): IRErrorExhaustiveStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IRErrorExhaustiveStatement(nval[0], nval[1], nval[3]);
    }
}

class IRTypeDeclSizeRangeCheckCStringStatement extends IRErrorTypedStringCheckStatement {
    readonly min: IRLiteralExpression | undefined;
    readonly max: IRLiteralExpression | undefined;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, min: IRLiteralExpression | undefined, max: IRLiteralExpression | undefined, strexp: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclSizeRangeCheckCStringStatement, file, sinfo, undefined, checkID, strexp);
        this.min = min;
        this.max = max;
    }

    static jsonEmit_IRTypeDeclSizeRangeCheckCStringStatement(exp: IRTypeDeclSizeRangeCheckCStringStatement): object {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);
        const cval = IRErrorTypedStringCheckStatement.jsonEmitMeta_IRErrorTypedStringCheckStatement(exp);

        return {
            ...nval,
            ...cval,
            min: exp.min === undefined ? null : IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.min),
            max: exp.max === undefined ? null : IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.max)
        };
    }

    static jsonParse_IRTypeDeclSizeRangeCheckCStringStatement(obj: any): IRTypeDeclSizeRangeCheckCStringStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);
        const cval = IRErrorTypedStringCheckStatement.jsonParseMeta_IRErrorTypedStringCheckStatement(obj);

        const strexp = IRImmediateExpression.jsonParse_IRSimpleExpression(cval[0]); 
        return new IRTypeDeclSizeRangeCheckCStringStatement(nval[0], nval[1], nval[3], obj.min !== null ? IRSimpleExpression.jsonParse_IRSimpleExpression(obj.min) : undefined, obj.max !== null ? IRSimpleExpression.jsonParse_IRSimpleExpression(obj.max) : undefined, strexp);
    }
}

class IRTypeDeclSizeRangeCheckUnicodeStringStatement extends IRErrorTypedStringCheckStatement {
    readonly min: IRLiteralExpression | undefined;
    readonly max: IRLiteralExpression | undefined;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, min: IRLiteralExpression | undefined, max: IRLiteralExpression | undefined, strexp: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclSizeRangeCheckUnicodeStringStatement, file, sinfo, undefined, checkID, strexp);
        this.min = min;
        this.max = max;
    }

    static jsonEmit_IRTypeDeclSizeRangeCheckUnicodeStringStatement(exp: IRTypeDeclSizeRangeCheckUnicodeStringStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);
        const sval = IRErrorTypedStringCheckStatement.jsonEmitMeta_IRErrorTypedStringCheckStatement(exp);

        return {
            ...nval,
            ...sval,
            min: exp.min === undefined ? null : IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.min),
            max: exp.max === undefined ? null : IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.max)
        };
    }

    static jsonParse_IRTypeDeclSizeRangeCheckUnicodeStringStatement(obj: any): IRTypeDeclSizeRangeCheckUnicodeStringStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);
        const sval = IRErrorTypedStringCheckStatement.jsonParseMeta_IRErrorTypedStringCheckStatement(obj);

        const strexp = IRImmediateExpression.jsonParse_IRSimpleExpression(sval[0]); 
        return new IRTypeDeclSizeRangeCheckUnicodeStringStatement(nval[0], nval[1], nval[3], obj.min !== null ? IRSimpleExpression.jsonParse_IRSimpleExpression(obj.min) : undefined, obj.max !== null ? IRSimpleExpression.jsonParse_IRSimpleExpression(obj.max) : undefined, strexp);
    }
}

class IRTypeDeclNumericRangeCheckStatement extends IRErrorCheckStatement {
    readonly min: IRLiteralExpression | undefined;
    readonly max: IRLiteralExpression | undefined;
    readonly numexp: IRImmediateExpression;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, min: IRLiteralExpression | undefined, max: IRLiteralExpression | undefined, numexp: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclNumericRangeCheckStatement, file, sinfo, undefined, checkID);
        this.min = min;
        this.max = max;
        this.numexp = numexp;
    }

    static jsonEmit_IRTypeDeclNumericRangeCheckStatement(exp: IRTypeDeclNumericRangeCheckStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval,
            min: exp.min === undefined ? null : IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.min),
            max: exp.max === undefined ? null : IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.max),
            numexp: IRImmediateExpression.jsonEmit_IRSimpleExpression(exp.numexp)
        };
    }

    static jsonParse_IRTypeDeclNumericRangeCheckStatement(obj: any): IRTypeDeclNumericRangeCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IRTypeDeclNumericRangeCheckStatement(nval[0], nval[1], nval[3], obj.min !== null ? IRSimpleExpression.jsonParse_IRSimpleExpression(obj.min) : undefined, obj.max !== null ? IRSimpleExpression.jsonParse_IRSimpleExpression(obj.max) : undefined, IRImmediateExpression.jsonParse_IRSimpleExpression(obj.numexp));
    }
}

class IRTypeDeclFormatCheckCStringStatement extends IRErrorTypedStringCheckStatement {
    readonly re: IRLiteralCRegexExpression;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, strexp: IRImmediateExpression, re: IRLiteralCRegexExpression,) {
        super(IRStatementTag.IRTypeDeclFormatCheckCStringStatement, file, sinfo, undefined, checkID, strexp);
        this.re = re;
    }

    static jsonEmit_IRTypeDeclFormatCheckCStringStatement(exp: IRTypeDeclFormatCheckCStringStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);
        const sval = IRErrorTypedStringCheckStatement.jsonEmitMeta_IRErrorTypedStringCheckStatement(exp);

        return {
            ...nval,
            ...sval,
            re: IRLiteralCRegexExpression.jsonEmit_IRLiteralCRegexExpression(exp.re)
        };
    }

    static jsonParse_IRTypeDeclFormatCheckCStringStatement(obj: any): IRTypeDeclFormatCheckCStringStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);
        const sval = IRErrorTypedStringCheckStatement.jsonParseMeta_IRErrorTypedStringCheckStatement(obj);

        return new IRTypeDeclFormatCheckCStringStatement(nval[0], nval[1], nval[3], ...sval, IRLiteralCRegexExpression.jsonParse_IRLiteralCRegexExpression(obj.re));
    }
}

class IRTypeDeclFormatCheckUnicodeStringStatement extends IRErrorTypedStringCheckStatement {
    readonly re: IRLiteralUnicodeRegexExpression;

    constructor(file: string, sinfo: IRSourceInfo, checkID: number, strexp: IRImmediateExpression, re: IRLiteralUnicodeRegexExpression) {
        super(IRStatementTag.IRTypeDeclFormatCheckUnicodeStringStatement, file, sinfo, undefined, checkID, strexp);
        this.re = re;
    }

    static jsonEmit_IRTypeDeclFormatCheckUnicodeStringStatement(exp: IRTypeDeclFormatCheckUnicodeStringStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);
        const sval = IRErrorTypedStringCheckStatement.jsonEmitMeta_IRErrorTypedStringCheckStatement(exp);

        return {
            ...nval,
            ...sval,
            re: IRLiteralUnicodeRegexExpression.jsonEmit_IRLiteralUnicodeRegexExpression(exp.re)
        };
    }

    static jsonParse_IRTypeDeclFormatCheckUnicodeStringStatement(obj: any): IRTypeDeclFormatCheckUnicodeStringStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);
        const sval = IRErrorTypedStringCheckStatement.jsonParseMeta_IRErrorTypedStringCheckStatement(obj);

        return new IRTypeDeclFormatCheckUnicodeStringStatement(nval[0], nval[1], nval[3], ...sval, IRLiteralUnicodeRegexExpression.jsonParse_IRLiteralUnicodeRegexExpression(obj.re));
    }
}

/* This calls the defined invariant check function for the target type decl on the provided value -- errors are reported from there */
class IRTypeDeclInvariantCheckStatement extends IRErrorCheckStatement {
    readonly tkey: string;
    readonly invariantidx: number;
    readonly targetValue: IRImmediateExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, tkey: string, invariantidx: number, targetValue: IRImmediateExpression) {
        super(IRStatementTag.IRTypeDeclInvariantCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.tkey = tkey;
        this.invariantidx = invariantidx;
        this.targetValue = targetValue;
    }

    static jsonEmit_IRTypeDeclInvariantCheckStatement(exp: IRTypeDeclInvariantCheckStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval,
            tkey: exp.tkey,
            invariantidx: exp.invariantidx,
            targetValue: IRImmediateExpression.jsonEmit_IRImmediateExpression(exp.targetValue)
        };
    }

    static jsonParse_IRTypeDeclInvariantCheckStatement(obj: any): IRTypeDeclInvariantCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IRTypeDeclInvariantCheckStatement(nval[0], nval[1], nval[2], nval[3], obj.tkey, obj.invariantidx, IRImmediateExpression.jsonParse_IRImmediateExpression(obj.targetValue));
    }
}

class IREntityInvariantCheckStatement extends IRErrorCheckStatement {
    readonly tkey: string
    readonly invariantidx: number;
    readonly args: IRImmediateExpression[];

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, tkey: string, invariantidx: number, args: IRImmediateExpression[]) {
        super(IRStatementTag.IREntityInvariantCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.tkey = tkey;
        this.invariantidx = invariantidx;
        this.args = args;
    }

    static jsonEmit_IREntityInvariantCheckStatement(exp: IREntityInvariantCheckStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval,
            tkey: exp.tkey,
            invariantidx: exp.invariantidx,
            args: exp.args.map(IRImmediateExpression.jsonEmit_IRImmediateExpression)
        };
    }

    static jsonParse_IREntityInvariantCheckStatement(obj: any): IREntityInvariantCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IREntityInvariantCheckStatement(nval[0], nval[1], nval[2], nval[3], obj.tkey, obj.invariantidx, obj.args.map(IRImmediateExpression.jsonParse_IRImmediateExpression));
    }
}

/* This asserts that the given precondition expression is true */
class IRPreconditionCheckStatement extends IRErrorCheckStatement {
    readonly ikey: string;
    readonly requiresidx: number;
    readonly args: IRImmediateExpression[];

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, ikey: string, requiresidx: number, args: IRImmediateExpression[]) {
        super(IRStatementTag.IRPreconditionCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.ikey = ikey;
        this.requiresidx = requiresidx;
        this.args = args;
    }

    static jsonEmit_IRPreconditionCheckStatement(exp: IRPreconditionCheckStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval,
            ikey: exp.ikey,
            requiresidx: exp.requiresidx,
            args: exp.args.map(IRImmediateExpression.jsonEmit_IRImmediateExpression)
        };
    }

    static jsonParse_IRPreconditionCheckStatement(obj: any): IRPreconditionCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IRPreconditionCheckStatement(nval[0], nval[1], nval[2], nval[3], obj.ikey, obj.requiresidx, obj.args.map(IRImmediateExpression.jsonParse_IRImmediateExpression));
    }
}

/* This asserts that the given postcondition expresssion is true */
class IRPostconditionCheckStatement extends IRErrorCheckStatement {
    readonly ikey: string;
    readonly ensuresidx: number;
    readonly args: IRImmediateExpression[];

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, ikey: string, ensuresidx: number, args: IRImmediateExpression[]) {
        super(IRStatementTag.IRPostconditionCheckStatement, file, sinfo, diagnosticTag, checkID);
        this.ikey = ikey;
        this.ensuresidx = ensuresidx;
        this.args = args;
    }

    static jsonEmit_IRPostconditionCheckStatement(exp: IRPostconditionCheckStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval,
            ikey: exp.ikey,
            ensuresidx: exp.ensuresidx,
            args: exp.args.map(IRImmediateExpression.jsonEmit_IRImmediateExpression)
        };
    }

    static jsonParse_IRPostconditionCheckStatement(obj: any): IRPostconditionCheckStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IRPostconditionCheckStatement(nval[0], nval[1], nval[2], nval[3], obj.ikey, obj.ensuresidx, obj.args.map(IRImmediateExpression.jsonParse_IRImmediateExpression));
    }
}

class IRAbortStatement extends IRErrorCheckStatement {
    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number) {
        super(IRStatementTag.IRAbortStatement, file, sinfo, diagnosticTag, checkID);
    }

    override isTerminalStatement(): boolean { return true; }

    static jsonEmit_IRAbortStatement(exp: IRAbortStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval
        };
    }

    static jsonParse_IRAbortStatement(obj: any): IRAbortStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IRAbortStatement(nval[0], nval[1], nval[2], nval[3]);
    }
}

class IRAssertStatement extends IRErrorCheckStatement {
    readonly cond: IRSimpleExpression;

    constructor(file: string, sinfo: IRSourceInfo, diagnosticTag: string | undefined, checkID: number, cond: IRSimpleExpression) {
        super(IRStatementTag.IRAssertStatement, file, sinfo, diagnosticTag, checkID);
        this.cond = cond;
    }

    static jsonEmit_IRAssertStatement(exp: IRAssertStatement): any {
        const nval = IRErrorCheckStatement.jsonEmitMeta_IRErrorCheckStatement(exp);

        return {
            ...nval,
            cond: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.cond)
        };
    }

    static jsonParse_IRAssertStatement(obj: any): IRAssertStatement {
        const nval = IRErrorCheckStatement.jsonParseMeta_IRErrorCheckStatement(obj);

        return new IRAssertStatement(nval[0], nval[1], nval[2], nval[3], IRSimpleExpression.jsonParse_IRSimpleExpression(obj.cond));
    }
}

class IRDebugStatement extends IRAtomicStatement {
    readonly oftype: IRTypeSignature;
    readonly dbgexp: IRSimpleExpression;

    readonly file: string;
    readonly line: number;

    constructor(oftype: IRTypeSignature, dbgexp: IRSimpleExpression, file: string, sinfo: IRSourceInfo) {
        super(IRStatementTag.IRDebugStatement);
        this.oftype = oftype;
        this.dbgexp = dbgexp;

        this.file = file;
        this.line = sinfo.line;
    }

    override isSimpleStatement(): boolean {
        return false;
    }

    static jsonEmit_IRDebugStatement(exp: IRDebugStatement): any {
        return {
            oftype: IRTypeSignature.jsonEmit_IRTypeSignature(exp.oftype),
            dbgexp: IRSimpleExpression.jsonEmit_IRSimpleExpression(exp.dbgexp),
            file: exp.file,
            line: exp.line
        };
    }

    static jsonParse_IRDebugStatement(obj: any): IRDebugStatement {
        return new IRDebugStatement(
            IRTypeSignature.jsonParse_IRTypeSignature(obj.oftype),
            IRSimpleExpression.jsonParse_IRSimpleExpression(obj.dbgexp),
            obj.file,
            obj.line
        );
    }
}

class IRBlockStatement extends IRStatement {
    readonly statements: IRStatement[];

    readonly livevars: string[];
    readonly livetemps: number[];

    constructor(statements: IRStatement[], livevars: string[], livetemps: number[]) {
        super(IRStatementTag.IRBlockStatement);
        this.statements = statements;
        this.livevars = livevars;
        this.livetemps = livetemps;
    }

    override isTerminalStatement(): boolean { 
        return this.statements.length > 0 && this.statements[this.statements.length - 1].isTerminalStatement(); 
    }

    override isSimpleStatement(): boolean {
        return this.statements.every(s => s.isSimpleStatement());
    }

    static jsonEmit_IRBlockStatement(exp: IRBlockStatement): any {
        return {
            statements: exp.statements.map((vv) => IRStatement.jsonEmit_IRStatement(vv)),
            livevars: exp.livevars,
            livetemps: exp.livetemps
        };
    }

    static jsonParse_IRBlockStatement(obj: any): IRBlockStatement {
        return new IRBlockStatement(
            obj.statements.map((vv: any) => IRStatement.jsonParse_IRStatement(vv)),
            obj.livevars,
            obj.livetemps
        );
    }
}

abstract class IRBody {
    constructor() {
    }

    abstract isSimpleBody(): boolean;

    static jsonEmit_IRBody(exp: IRBody): [string, object] {
        if(exp instanceof IRAbstractBody) {
            return ["AbstractBody", IRAbstractBody.jsonEmit_IRAbstractBody(exp)];
        }
        else if(exp instanceof IRBuiltinBody) {
            return ["BuiltinBody", IRBuiltinBody.jsonEmit_IRBuiltinBody(exp)];
        }
        else if(exp instanceof IRHoleBody) {
            return ["HoleBody", IRHoleBody.jsonEmit_IRHoleBody(exp)];
        }
        else if(exp instanceof IRStandardBody) {
            return ["StandardBody", IRStandardBody.jsonEmit_IRStandardBody(exp)];
        }
        else {
            throw new Error(`Unknown body type: ${exp}`);
        }
    }

    static jsonParse_IRBody(obj: any): IRBody {
        const kind = obj[0];
        const value = obj[1];

        switch(kind) {
            case "AbstractBody": {
                return IRAbstractBody.jsonParse_IRAbstractBody(value);
            }
            case "BuiltinBody": {
                return IRBuiltinBody.jsonParse_IRBuiltinBody(value);
            }
            case "HoleBody": {
                return IRHoleBody.jsonParse_IRHoleBody(value);
            }
            case "StandardBody": {
                return IRStandardBody.jsonParse_IRStandardBody(value);
            }
            default: {
                assert(false, `Unknown body type: ${kind}`);
            }
        }
    }
}

class IRAbstractBody extends IRBody {
    constructor() {
        super();
    }

    override isSimpleBody(): boolean {
        return false;
    }

    static jsonEmit_IRAbstractBody(exp: IRAbstractBody): any {
        return {};
    }

    static jsonParse_IRAbstractBody(obj: any): IRAbstractBody {
        return new IRAbstractBody();
    }
}

class IRBuiltinBody extends IRBody {
    readonly builtin: string;
    readonly biterms: [string, IRTypeSignature][];

    constructor(builtin: string, biterms: [string, IRTypeSignature][]) {
        super();
        this.builtin = builtin;
        this.biterms = biterms;
    }

    override isSimpleBody(): boolean {
        return false;
    }

    static jsonEmit_IRBuiltinBody(exp: IRBuiltinBody): any {
        return {
            builtin: exp.builtin,
            biterms: exp.biterms.map(([name, t]) => [name, IRTypeSignature.jsonEmit_IRTypeSignature(t)])
        };
    }

    static jsonParse_IRBuiltinBody(obj: any): IRBuiltinBody {
        return new IRBuiltinBody(
            obj.builtin,
            obj.biterms.map(([name, t]: [string, any]) => [name, IRTypeSignature.jsonParse_IRTypeSignature(t)])
        );
    }
}

class IRHoleBody extends IRBody {
    readonly startline: number;
    readonly endline: number;

    readonly hname: string | undefined;
    readonly doccomment: string | undefined;
    readonly samplesfile: string | undefined;
    
    constructor(startline: number, endline: number, hname: string | undefined, doccomment: string | undefined, samplesfile: string | undefined) {
        super();
        this.startline = startline;
        this.endline = endline;
        this.hname = hname;
        this.doccomment = doccomment;
        this.samplesfile = samplesfile;
    }

    override isSimpleBody(): boolean {
        return false;
    }

    static jsonEmit_IRHoleBody(exp: IRHoleBody): any {
        return {
            startline: exp.startline,
            endline: exp.endline,
            hname: exp.hname,
            doccomment: exp.doccomment,
            samplesfile: exp.samplesfile
        };
    }

    static jsonParse_IRHoleBody(obj: any): IRHoleBody {
        return new IRHoleBody(
            obj.startline,
            obj.endline,
            obj.hname,
            obj.doccomment,
            obj.samplesfile
        );
    }
}

class IRStandardBody extends IRBody {
    readonly statements: IRStatement[];

    constructor(statements: IRStatement[]) {
        super();
        this.statements = statements;
    }

    override isSimpleBody(): boolean {
        return this.statements.every(s => s.isSimpleStatement());
    }

    static jsonEmit_IRStandardBody(exp: IRStandardBody): any {
        return {
            statements: exp.statements.map(IRStatement.jsonEmit_IRStatement)
        };
    }

    static jsonParse_IRStandardBody(obj: any): IRStandardBody {
        return new IRStandardBody(
            obj.statements.map(IRStatement.jsonParse_IRStatement)
        );
    }
}

export {
    IRExpressionTag, IRExpression, IRLiteralExpression, IRImmediateExpression, IRSimpleExpression,
    
    IRLiteralNoneExpression, IRLiteralBoolExpression,
    IRLiteralIntegralNumberExpression, IRLiteralNatExpression, IRLiteralIntExpression, IRLiteralChkNatExpression, IRLiteralChkIntExpression,
    IRLiteralRationalExpression, IRLiteralFloatingPointExpression, IRLiteralFloatExpression, IRLiteralDecimalExpression,
    IRLiteralDecimalDegreeExpression, IRLiteralLatLongCoordinateExpression, IRLiteralComplexExpression,
    IRLiteralByteBufferExpression, 
    IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRLiteralSHAContentHashExpression,
    IRDateRepresentation, IRTimeRepresentation, IRLiteralTZDateTimeExpression, IRLiteralTAITimeExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralLogicalTimeExpression, IRLiteralISOTimeStampExpression,
    IRDeltaDateRepresentation, IRDeltaTimeRepresentation, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaSecondsExpression, IRLiteralDeltaLogicalTimeExpression,
    IRLiteralUnicodeRegexExpression, IRLiteralCRegexExpression,
    IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralUnicodeCharExpression,
    IRLiteralCStringExpression, IRLiteralStringExpression,

    IRFormatStringComponent, IRFormatStringTextComponent, IRFormatStringArgComponent,
    IRLiteralFormatStringExpression, IRLiteralFormatCStringExpression,
    IRLiteralTypedExpression, IRLiteralTypedStringExpression, IRLiteralTypedCStringExpression,

    IRAccessEnvHasExpression, IRAccessEnvGetExpression, IRAccessEnvTryGetExpression,
    IRTaskAccessIDExpression, IRTaskAccessParentIDExpression,

    IRAccessConstantExpression, IRAccessEnumExpression,
    IRAccessParameterVariableExpression, IRAccessLocalVariableExpression, IRAccessCapturedVariableExpression, IRAccessTempVariableExpression,
    
    IRAccessTypeDeclValueExpression, IRConstructSafeTypeDeclExpression,

    IRConstructorSomeTypeExpression, IRConstructorOkTypeExpression, IRConstructorFailTypeExpression, IRConstructorAPISuccessTypeExpression, IRConstructorMapEntryTypeExpression,

    IRConstructExpression,

    IRConstructorStandardEntityExpression,
    IRConstructorLambdaExpression,
    IRConstructorEListExpression,
    IRConstructorListEmptyExpression, IRConstructorListPassthroughExpression, IRConstructorListSingletonsExpression, IRConstructorListMixedExpression,
    IRConstructorMapEmptyExpression, IRConstructorMapSingletonsExpression,

    IRAccessFieldExpression, IRAccessFieldSpecialExpression, IRAccessFieldDirectExpression, IRAccessFieldVirtualExpression, IRAccessEListIndexExpression,

    IRImplicitInvokeArgPassKind,
    IRInvokeExpression, IRInvokeDirectExpression, IRInvokeImplicitsExpression, IRInvokeSimpleExpression, IRInvokeSimpleWithImplicitsExpression, IRInvokeVirtualSimpleExpression, IRInvokeVirtualWithImplicitsExpression,

    IRInvokeCallAgentOrAPIExpression, IRInvokeTaskActionExpression,

    IRInterpolateFormatCStringExpression, IRInterpolateFormatStringExpression,

    IRUnaryOpExpression, IRPrefixNotOpExpression, IRPrefixNegateOpExpression, IRPrefixPlusOpExpression,
    IRBinOpExpression, IRBinAddExpression, IRBinSubExpression, IRBinMultExpression, IRBinDivExpression,
    IRNumericComparisonExpression, IRNumericEqExpression, IRNumericNeqExpression, IRNumericLessExpression, IRNumericLessEqExpression, IRNumericGreaterExpression, IRNumericGreaterEqExpression,
    IRIsNoneOptionExpression, IRIsNotNoneOptionExpression, IRIsOptionEqValueExpression, IRIsOptionNeqValueExpression, IRIsSomeEqValueExpression, IRIsSomeNeqValueExpression,
    IRKeyComparisonExpression, IRBinKeyEqDirectExpression, IRBinKeyNeqDirectExpression, IRBinKeyLessDirectExpression,
    IRLogicOpExpression, IRLogicAndExpression, IRLogicOrExpression,

    IRLogicSimpleConditionalExpression,

    IRLiteralOptionOfNoneExpression, IRConstructOptionFromSomeExpression, IRExtractSomeFromOptionExpression, IRExtractSomeValueFromOptionExpression,
    IRConstructResultFromOkExpression, IRConstructResultFromFailExpression, IRExtractOkFromResultExpression, IRExtractOkValueFromResultExpression, IRExtractFailFromResultExpression, IRExtractFailValueFromResultExpression,
    IRConceptRepresentationOfTypeExpression, IRIsConceptRepresentationOfTypeExpression, IRIsNotConceptRepresentationOfTypeExpression, IRIsConceptRepresentationSubtypeOfTypeExpression, IRIsNotConceptRepresentationSubtypeOfTypeExpression, IRStaticIsTypeSubtypeOfExpression,
    IRBoxEntityToConceptRepresentationExpression, IRUnboxEntityFromConceptRepresentationExpression, IRConvertConceptRepresentationExpression,

    IRStatementTag, IRStatement, IRAtomicStatement, IRReturnSimpleStatement,
    IRErrorCheckStatement, IRErrorBinArithCheckStatement,

    IRNopStatement,
    IRTempAssignExpressionStatement, IRTempAssignStdInvokeStatement, IRTempAssignRefInvokeStatement, IRTempAssignDirectConstructorStatement,

    IRVariableDeclarationStatement, 
    IRVariableInitializationStatement, IRVariableInitializationDirectInvokeStatement, IRVariableInitializationDirectInvokeWithImplicitStatement, IRVariableInitializationDirectConstructorStatement, IRVariableInitializationDirectConstructorWithBoxStatement,
    IRVariableAssignmentStatement, IRVariableAssignmentDirectInvokeStatement, IRVariableAssignmentDirectInvokeWithImplicitStatement, IRVariableAssignmentDirectConstructorStatement, IRVariableAssignmentDirectConstructorWithBoxStatement,
    
    IRUpdateLocalDirectStatement, IRUpdateParamDirectStatement,

    IRReturnVoidSimpleStatement, IRReturnValueSimpleStatement, IRReturnDirectInvokeStatement, IRReturnDirectConstructStatement, IRReturnDirectConstructWithBoxStatement,
    
    IRVoidInvokeStatement,

    IRChkLogicImpliesShortCircuitStatement,
    IRLogicConditionalStatement,

    IRSimpleIfStatement, IRSimpleIfElseStatement,
    IRMatchExactStatement, IRMatchGeneralStatement,

    IRErrorAdditionBoundsCheckStatement, IRErrorSubtractionBoundsCheckStatement, IRErrorMultiplicationBoundsCheckStatement, IRErrorDivisionByZeroCheckStatement,
    IRErrorTypeAssertionCheckStatement, IRErrorExhaustiveStatement,
    IRErrorTypedStringCheckStatement, IRTypeDeclSizeRangeCheckCStringStatement, IRTypeDeclSizeRangeCheckUnicodeStringStatement, IRTypeDeclNumericRangeCheckStatement, IRTypeDeclFormatCheckCStringStatement, IRTypeDeclFormatCheckUnicodeStringStatement,

    IRTypeDeclInvariantCheckStatement, IREntityInvariantCheckStatement,
    IRPreconditionCheckStatement, IRPostconditionCheckStatement,
    IRAbortStatement, IRAssertStatement, IRDebugStatement,

    IRBlockStatement,
    IRBody, IRAbstractBody, IRBuiltinBody, IRHoleBody, IRStandardBody
};
