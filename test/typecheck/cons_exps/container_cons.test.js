"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Container Constructor (List)", () => {
    it("should check list constructors", function () {
        checkTestFunction("function main(): List<Int> { return List<Int>{}; }");
        checkTestFunction("function main(): List<Int> { return List<Int>{1i, 2i, 3i}; }");
        checkTestFunction("function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }");
    });

    it("should fail list constructors", function () {
        checkTestFunctionError("function main(): List<Int> { return List<Int>{x=2i}; }", 'Rest argument 0 expected to be container of type Int');
        checkTestFunctionError("function main(): List<Int> { return List<Int>{2n}; }", 'Argument 0 expected type Int');
    });
});
