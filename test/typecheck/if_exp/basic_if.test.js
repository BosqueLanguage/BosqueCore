"use strict";

import { checkTestExp, checkTestExpError, checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple if-expression", () => {
    it("should check simple", function () {
        checkTestExp("if(1n != 2n) then 2i else 3i + 5i", "Int");
        checkTestExp("if(3n != 2n) then 2i else (3i + 5i)", "Int");
        checkTestExp("(if(1n == 2n) then 2i else 3i) + 5i", "Int");
    });

    it("should check expressions w/ itest", function () {
        checkTestFunction("function main(x: Int?): Int { return if(x)!none then 2i else 3i; }");
        checkTestFunction("function main(x: Int?): Int { return if(x)some then 2i else 3i; }");
        checkTestFunction("function main(x: Int?): Int { return if(x)<Some<Int>> then 2i else 3i; }");

        checkTestFunction("function main(x: Int?): Int { return if(x)@!none then $x else 3i; }");
        checkTestFunction("function main(x: Int): Int? { return if(x < 3i) then none else some(x); }");
        checkTestFunction("function main(x: Int): Int { return if(if(x < 3i) then none else some(x))@!none then $_ else 3i; }");
        checkTestFunction("function main(x: Int?): Int? { return if($y = x)@<Some<Int>> then $y else some(3i); }");
    });

    it("should fail not bool test", function () {
        checkTestExpError("if(3i) then 3i else 2i", "Int", "If test requires a Bool type");
    });

    it("should fail bad true", function () {
        checkTestExpError("if(1n == 2n) then true else 2i", "Int", "Expected a return value of type Int but got Any");
    });

    it("should fail bad false", function () {
        checkTestExpError("if(1n < 2n) then 3i else none", "Int", "Expected a return value of type Int but got Any");
    });

    it("should fail always true", function () {
        checkTestFunctionError("function main(x: Int): Int { return if(x)@<Bool> then 2i else 3i; }", "Test is never true -- true branch of if is unreachable");
    });

    it("should fail always false", function () {
        checkTestFunctionError("function main(x: Int): Int { return if(x)@<Any> then 2i else 3i; }", "Test is never false -- false branch of if is unreachable");
    });
});