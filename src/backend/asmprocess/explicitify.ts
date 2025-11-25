import { Expression, ExpressionTag } from "../../frontend/body";

import assert from "node:assert";

class Explicitifier {
    
    
    private explicitifyExpression(exp: Expression): Expression {
        const ttag = exp.tag;

        if(ttag === ExpressionTag.LiteralNoneExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralBoolExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralNatExpression || ttag === ExpressionTag.LiteralIntExpression || ttag === ExpressionTag.LiteralChkNatExpression || ttag === ExpressionTag.LiteralChkIntExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralRationalExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralFloatExpression || ttag === ExpressionTag.LiteralDecimalExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralDecimalDegreeExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralLatLongCoordinateExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralComplexNumberExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralByteBufferExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralUUIDv4Expression || ttag === ExpressionTag.LiteralUUIDv7Expression || ttag === ExpressionTag.LiteralSHAContentHashExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralTZDateTimeExpression || ttag === ExpressionTag.LiteralTAITimeExpression || ttag === ExpressionTag.LiteralPlainDateExpression || ttag === ExpressionTag.LiteralPlainTimeExpression || ttag === ExpressionTag.LiteralLogicalTimeExpression || ttag === ExpressionTag.LiteralISOTimeStampExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralDeltaISOTimeStampExpression || ttag === ExpressionTag.LiteralDeltaSecondsExpression || ttag === ExpressionTag.LiteralDeltaLogicalExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralUnicodeRegexExpression || ttag === ExpressionTag.LiteralCRegexExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralByteExpression || ttag === ExpressionTag.LiteralCCharExpression || ttag === ExpressionTag.LiteralUnicodeCharExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralStringExpression || ttag === ExpressionTag.LiteralCStringExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralFormatStringExpression || ttag === ExpressionTag.LiteralFormatCStringExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralTypeDeclValueExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralTypedStringExpression) {
            return exp;
        }
        else if(ttag === ExpressionTag.LiteralTypedCStringExpression) {
            return exp;
        }
        else {
            assert(false, `Explicitifier: Unsupported expression type -- ${exp.tag}`);
        }
    }
}

export {
    Explicitifier
};
