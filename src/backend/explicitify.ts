import { Expression, ExpressionTag } from "../frontend/body";

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
        else if(ttag === ExpressionTag.LiteralNatExpression || ttag === ExpressionTag.LiteralIntExpression || ttag === ExpressionTag.LiteralBigNatExpression || ttag === ExpressionTag.LiteralBigIntExpression) {
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
        else {
            assert(false, `Explicitifier: Unsupported expression type -- ${exp.tag}`);
        }
    }
}

export {
    Explicitifier
};
