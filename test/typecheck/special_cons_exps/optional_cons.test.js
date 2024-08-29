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

describe ("Checker -- Special Constructor Result", () => {
    it("should check ok with simple infer", function () {
        checkTestExp("ok(3i)", "Result<Int, Bool>::Ok");
        checkTestExp("ok(3i)", "Result<Int, Bool>");
    });

    it("should check err with simple infer", function () {
        checkTestExp("fail(true)", "Result<Int, Bool>::Fail");
        checkTestExp("fail(false)", "Result<Int, Bool>");
    });

    it("should fail cannot convert", function () {
        checkTestExpError("ok(3i)", "Int", "Cannot infer type for special Ok constructor -- got Int");
        checkTestExpError("fail(3i)", "Int", "Cannot infer type for special Err constructor -- got Int");
        checkTestExpError("ok(3n)", "Result<Int, Bool>", "Ok constructor argument is not a subtype of Int");
    });
});

describe ("Checker -- Special Constructor infer in if-else and assign positions", () => {
    it("should check with if-else", function () {
        checkTestExp("if(true) then ok(3i) else err(false)", "Result<Int, Bool>");
        checkTestExp("if(false) then none else some(3i)", "Option<Int>");
    });

    it("should check err with simple infer", function () {
        checkTestFunction("function main(): Option<Int> { let x: Option<Int> = none; return x; }");
        checkTestFunction("function main(): Option<Int> { var x: Option<Int> = some(1i); return x; }");
    });
});

