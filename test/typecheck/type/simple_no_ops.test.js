"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- type decl of bool", () => {
    it("should check bool type decl", function () {
        checkTestFunction('type Flag = Bool; function main(): Flag { return true<Flag>; }'); 
    });

    it("should fail not bool", function () {
        checkTestFunctionError("type Flag = Bool; function main(): Flag { return 3i<Flag>; }", "Literal value is not the same type (Int) as the base type (Bool)");
    });
});

describe ("Checker -- type decl of number", () => {
    it("should check numeric type decls", function () {
        checkTestFunction('type NVal = Int; function main(): NVal { return -2i<NVal>; }');
        checkTestFunction('type FVal = Float; function main(): FVal { return 0.0f<FVal>; }');    
    });

    it("should fail not int", function () {
        checkTestFunctionError("type NVal = Int; function main(): NVal { return 3n<NVal>; }", "Literal value is not the same type (Nat) as the base type (Int)");
    });
});

describe ("Checker -- type decl of number with value", () => {
    it("should check numeric type decls", function () {
        checkTestFunction('type NVal = Int; function main(): Int { let x = -2i<NVal>; return x.value; }');    
    });

    it("should fail not nat", function () {
        checkTestFunctionError('type NVal = Int; function main(): Nat { let x = -2i<NVal>; return x.value; }', "Expected a return value of type Nat but got Int");
    });
});
