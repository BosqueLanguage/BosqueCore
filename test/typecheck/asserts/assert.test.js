"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple Abort", () => {
    it("should check abort", function () {
        checkTestFunction("function main(): Int { if(false) { abort; } return 1i; }");
    });
});

describe ("Checker -- Simple Assert", () => {
    it("should check simple assert", function () {
        checkTestFunction("function main(): Int { assert 1i < 3i; return 0i; }");
    });

    it("should fail not boolean type", function () {
        checkTestFunctionError("function main(): Int { assert 3i; return 0i; }", "Expected a boolean type for assert condition but got Int");
    });
});

describe ("Checker -- Simple Validate", () => {
    it("should check simple validate", function () {
        checkTestFunction("function main(): Int { validate 1i < 3i; return 0i; }");
    });

    it("should fail not boolean type", function () {
        checkTestFunctionError("function main(): Int { validate 1i; return 0i; }", "Expected a boolean type for validate condition but got Int");
    });
});
