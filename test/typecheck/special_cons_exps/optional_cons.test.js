"use strict";

import { checkTestExp, checkTestExpError, checkTestFunction } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Special Constructor Optional", () => {
    it("should check none with simple infer", function () {
        checkTestExp("none", "None");
        checkTestExp("none", "Int?");
    });

    it("should check some with simple infer", function () {
        checkTestExp("some(3i)", "Some<Int>");
        checkTestExp("some(3i)", "Int?");
    });

    it("should check some w/o infer", function () {
        checkTestExp("none", "Any");
        checkTestExp("some(3i)", "Any");
    });

    it("should fail cannot convert", function () {
        checkTestExpError("none", "Int", "Expected a return value of type Int but got None");
        checkTestExpError("some(3i)", "Int", "Expected a return value of type Int but got Some<Int>");
        checkTestExpError("some(3n)", "Int?", "Some constructor argument is not a subtype of Int");
    });
});

describe ("Checker -- Special Constructor Result", () => {
    it("should check ok with simple infer", function () {
        checkTestExp("ok(3i)", "Result<Int, Bool>::Ok");
        checkTestExp("ok(3i)", "Result<Int, Bool>");
    });

    it("should check err with simple infer", function () {
        checkTestExp("err(true)", "Result<Int, Bool>::Err");
        checkTestExp("err(false)", "Result<Int, Bool>");
    });

    it("should fail cannot convert", function () {
        checkTestExpError("ok(3i)", "Int", "Cannot infer type for special Ok constructor -- got Int");
        checkTestExpError("err(3i)", "Int", "Cannot infer type for special Err constructor -- got Int");
        checkTestExpError("ok(3n)", "Result<Int, Bool>", "Ok constructor argument is not a subtype of Int");
    });

    it("should fail check some w/o infer", function () {
        checkTestExpError("ok(3i)", "Any", "Cannot infer type for special Ok constructor -- got Any");
        checkTestExpError("err(false)", "Any", "Cannot infer type for special Err constructor -- got Any");
    });
});

describe ("Checker -- Special Constructor infer in if-else and assign positions", () => {
    it("should check with if-else", function () {
        checkTestExp("if(true) then ok(3i) else err(false)", "Result<Int, Bool>");
        checkTestExp("if(false) then none else some(3i)", "Int?");
    });

    it("should check err with simple infer", function () {
        checkTestFunction("function main(): Int? { let x: Int? = none; return x; }");
        checkTestFunction("function main(): Int? { var x: Int? = some(1i); return x; }");
    });
});

