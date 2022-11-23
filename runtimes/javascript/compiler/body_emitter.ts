import * as assert from "assert";

import { TIRLiteralBoolExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression } from "../../../frontend/tree_ir/tir_body";

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
            xxxx;
        }
        else if(exp.etype === "Nat") {
            xxxx;
        }
        else if(exp.etype === "BigNat") {
            xxxx;
        }
        else {
            assert(exp.etype === "BigInt", "Unknown type TIRLiteralIntegralExpression");
        }
    }

    private emitLiteralRationalExpression = "LiteralRationalExpression",
    private emitLiteralFloatPointExpression = "LiteralFloatExpression",
    private emitLiteralRegexExpression = "LiteralRegexExpression",
}

export {
    BodyEmitter
};
