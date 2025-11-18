import { Expression, ExpressionTag, LiteralSimpleExpression } from "../frontend/body";
import { IRExpression, IRLiteralBigIntExpression, IRLiteralBigNatExpression, IRLiteralBoolExpression, IRLiteralComplexExpression, IRLiteralDecimalExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralLatLongCoordinateExpression, IRLiteralNatExpression, IRLiteralNoneExpression, IRLiteralRationalExpression, IRStatement } from "./irbody";

import assert from "node:assert";

class ASMToIRConverter {
    pendingblocks: IRStatement[][];

    constructor() {
        this.pendingblocks = [];
    }

    private flattenExpression(exp: Expression): IRExpression {
        const ttag = exp.tag;

        if(ttag === ExpressionTag.LiteralNoneExpression) {
            return new IRLiteralNoneExpression();
        }
        else if(ttag === ExpressionTag.LiteralBoolExpression) {
            return new IRLiteralBoolExpression((exp as LiteralSimpleExpression).value === "true");
        }
        else if(ttag === ExpressionTag.LiteralNatExpression) {
            return new IRLiteralNatExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralIntExpression) {
            return new IRLiteralIntExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralBigNatExpression) {
            return new IRLiteralBigNatExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralBigIntExpression) {
            return new IRLiteralBigIntExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralRationalExpression) {
            const rrval = (exp as LiteralSimpleExpression).value;
            const slpos = rrval.indexOf("/");
            
            return new IRLiteralRationalExpression(rrval.slice(0, slpos), rrval.slice(slpos + 1, -1));
        }
        else if(ttag === ExpressionTag.LiteralFloatExpression) {
            return new IRLiteralFloatExpression((exp as LiteralSimpleExpression).value);
        }
        else if(ttag === ExpressionTag.LiteralDecimalExpression) {
            return new IRLiteralDecimalExpression((exp as LiteralSimpleExpression).value);
        }
        else if(ttag === ExpressionTag.LiteralDecimalDegreeExpression) {
            return new IRLiteralDecimalExpression((exp as LiteralSimpleExpression).value.slice(0, -2));
        }
        else if(ttag === ExpressionTag.LiteralLatLongCoordinateExpression) {
            const latsplit = (exp as LiteralSimpleExpression).value.indexOf("lat");
            return new IRLiteralLatLongCoordinateExpression((exp as LiteralSimpleExpression).value.slice(0, latsplit), (exp as LiteralSimpleExpression).value.slice(latsplit + 3, -4));
        }
        else if(ttag === ExpressionTag.LiteralComplexNumberExpression) {
            const cnv = (exp as LiteralSimpleExpression).value;
            let spos = cnv.lastIndexOf("+");
            if(spos === -1) {
                spos = cnv.lastIndexOf("-");
            }

            return new IRLiteralComplexExpression(cnv.slice(0, spos), cnv.slice(spos, -1));
        }
        else {
            assert(false, `ASMToIRConverter: Unsupported expression type -- ${exp.tag}`);
        }
    }
}

export {
    ASMToIRConverter
};
