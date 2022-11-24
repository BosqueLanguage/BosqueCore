import * as assert from "assert";

import { TIRExpression, TIRExpressionTag, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression } from "../../../frontend/tree_ir/tir_body";

class BodyEmitter {
    constructor() {
    }

    private emitLiteralNoneExpression(exp: TIRLiteralNoneExpression): string {
        return "null";
    }

    private emitLiteralNothingExpression(exp: TIRLiteralNothingExpression): string {
        return "undefined";
    }
    private emitLiteralBoolExpression(exp: TIRLiteralBoolExpression): string {
        return exp.value ? "true" : "false";
    }

    private emitLiteralIntegralExpression(exp: TIRLiteralIntegralExpression): string {
        if(exp.etype === "Nat") {
            return exp.expstr; //n suffix makes a bitint 
        }
        else if(exp.etype === "Int") {
            return exp.expstr.slice(0, exp.expstr.length - 1) + "n"; //n suffix makes it a bigint
        }
        else if(exp.etype === "BigNat") {
            return exp.expstr.slice(0, exp.expstr.length - 1) + "n"; //n suffix makes it a bigint
        }
        else {
            assert(exp.etype === "BigInt", "Unknown type TIRLiteralIntegralExpression");
            return exp.expstr.slice(0, exp.expstr.length - 1) + "n"; //n suffix makes it a bigint
        }
    }

    private emitLiteralRationalExpression(exp: TIRLiteralRationalExpression): string {
        return `new Fraction("${exp.value.slice(0, exp.value.length - 1)}")`;
    }

    private emitLiteralFloatPointExpression(exp: TIRLiteralFloatPointExpression): string {
        if(exp.etype === "Float") {
            return exp.value.slice(0, exp.value.length - 1);
        }
        else {
            assert(exp.etype === "Decimal", "Unknown type TIRLiteralFloatPointExpression");
            return `new Decimal(${exp.value.slice(0, exp.value.length - 1)})`;
        }
    }

    private emitLiteralRegexExpression(exp: TIRLiteralRegexExpression): string {
        return exp.value.restr;
    }

    public emitExpression(exp: TIRExpression, toplevel?: boolean): string {
        switch (exp.tag) {
            case TIRExpressionTag.LiteralNoneExpression: {
                return this.emitLiteralNoneExpression(exp as TIRLiteralNoneExpression);
            }
            case TIRExpressionTag.LiteralNothingExpression: {
                return this.emitLiteralNothingExpression(exp as TIRLiteralNothingExpression);
            }
            case TIRExpressionTag.LiteralBoolExpression: {
                return this.emitLiteralBoolExpression(exp as TIRLiteralBoolExpression);
            }
            case TIRExpressionTag.LiteralIntegralExpression: {
                return this.emitLiteralIntegralExpression(exp as TIRLiteralIntegralExpression);
            }
            case TIRExpressionTag.LiteralRationalExpression: {
                return this.emitLiteralRationalExpression(exp as TIRLiteralRationalExpression);
            }
            case TIRExpressionTag.LiteralFloatPointExpression: {
                return this.emitLiteralFloatPointExpression(exp as TIRLiteralFloatPointExpression);
            }
            case TIRExpressionTag.LiteralRegexExpression: {
                return this.emitLiteralRegexExpression(exp as TIRLiteralRegexExpression);
            }

            default: {
                assert(false, `Unknown expression kind ${exp.tag}`);
                return `[UNKNOWN TAG ${exp.tag}]`
            }
        }
    }
}

export {
    BodyEmitter
};
