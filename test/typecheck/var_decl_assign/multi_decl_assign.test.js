"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- multi declare-assign only", () => {
    it("should check multi declare-assign", function () {
        checkTestFunction("function main(): Int { var x: Int, y: Bool = 1i, true; return x; }");
        checkTestFunction("function main(): Int { var x: Int, j: Bool = 1i, true; return x; }");
        
        checkTestFunction("function main(): Int { var x, y = 1i, true; return x; }");

        checkTestFunction("function main(): Int { var x: Int, k, z: Int = 1i, true, 0i; return x; }");
    });

    it("should check multi declare-assign from elist", function () {
        checkTestFunction("function main(): Int { var x: Int, y: Bool = (|1i, true|); return x; }");
        checkTestFunction("function main(): Int { var x: Int, _: Bool = (|1i, true|); return x; }");
        
        checkTestFunction("function main(): Int { var x, y = (|1i, true|); return x; }");
        checkTestFunction("function main(): Int { var x, _ = (|1i, true|); return x; }");

        checkTestFunction("function main(): Int { var x, _, _ = (|1i, true, false|); return x; }");
    });

    it("should fail multi declare-assign", function () {
        checkTestFunctionError("function main(): Int { var x: Int, y: Bool = 1i, true; return y; }", "Expected a return value of type Int but got Bool");
        checkTestFunctionError("function main(): Int { var x: Int, y: Bool = 1i; return x; }", 'Expected a EList for multi-variable initialization');
    });
});

describe ("Checker -- multi assign", () => {
    it("should check multi assign", function () {
        checkTestFunction("function main(): Int { var x: Int = 1i; var y: Bool; x, y = 2i, false; return x; }");

        checkTestFunction("function main(): Int { var x: Int = 1i; x, _ = (|2i, false|); return x; }");
    });

    it("should check multi assign fail", function () {
        checkTestFunctionError("function main(): Int { var x: Int = 1i; x, _ = 2i, false; return x; }", "Cannot use _ for variable assignment with multiple explicit expressions!!!");
    });
});
