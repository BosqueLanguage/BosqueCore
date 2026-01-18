
"use strict";

import { checkTestExp, checkTestExpError, checkTestFunction } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Special Constructor Optional", () => {
    it("should check none with simple infer", function () {
        checkTestExp("none", "None");
        checkTestExp("none", "Option<Int>");
    });

    it("should check some with simple infer", function () {
        checkTestExp("some(3i)", "Some<Int>");
        checkTestExp("some(3i)", "Option<Int>");
    });

    it("should fail cannot convert", function () {
        checkTestExpError("none", "Int", "Expected a return value of type Int but got None");
        checkTestExpError("some(3i)", "Int", "Expected a return value of type Int but got Some<Int>");
        checkTestExpError("some(3n)", "Option<Int>", "Some constructor argument is not a subtype of Int");
    });
});


describe ("Checker -- Special Constructor infer assign positions", () => {
    it("should check fail with simple infer", function () {
        checkTestFunction("function main(): Option<Int> { let x: Option<Int> = none; return x; }");
        checkTestFunction("function main(): Option<Int> { var x: Option<Int> = some(1i); return x; }");
    });
});
