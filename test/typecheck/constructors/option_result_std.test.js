"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Constructable Constructor (Option)", () => {
    it("should check option constructors", function () {
        checkTestFunction("function main(): Some<Int> { return Some<Int>{2i}; }");
        checkTestFunction("function main(): Option<Int> { return Some<Int>{2i}; }");
    });

    it("should fail option constructors", function () {
        checkTestFunctionError("function main(): Option<Int> { return Some<Int>{}; }", 'Some constructor expects 1 argument');
        checkTestFunctionError("function main(): Option<Int> { return Some<Int>{2i, false}; }", 'Some constructor expects 1 argument');
    });
});
