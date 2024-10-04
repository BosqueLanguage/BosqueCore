"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";


describe ("Checker -- elist return", () => {
    it("should check elist returns", function () {
        checkTestFunction('function foo(): (|Int, Bool|) { return (|2i, false|); } function main(): Int { return foo().0; }');
        checkTestFunction('function foo(): (|Int, Bool|) { return 2i, false; } function main(): Int { return foo().0; }');
    });

    it("should check elist returns w/ convert", function () {
        checkTestFunction('function foo(): (|Option<Int>, Bool|) { return (|some(2i), false|); } function main(): Int { return foo().0@some; }');
        checkTestFunction('function foo(): (|Option<Int>, Bool|) { return some(2i), false; } function main(): Int { return foo().0@some; }');
    });

    it("should check fail elist returns", function () {
        checkTestFunctionError('function foo(): (|Int, Bool|) { return (|2i, 3i|); } function main(): Int { return foo().0; }', 'Expected a return value of type (|Int, Bool|) but got (|Int, Int|)');
        checkTestFunctionError('function foo(): (|Int, Int, Int|) { return 2i, 3i; } function main(): Int { return foo().0; }', 'Mismatch in number of return values and expected return types');
    });
});
