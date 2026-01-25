"use strict";

import { checkTestFunction, checkTestFunctionError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- If Statement", () => {
    it("should check simple ifs", function () {
        checkTestFunction("function main(): Int { if(true) { return 3i; } return 1i; }");

        checkTestFunctionError("function main(): Int { if(3i) { return 3i; } return 1i; }", 'Guard expression does not evaluate to boolean');
        checkTestFunctionError("function main(): Int { if(true) { return true; } return 1i; }", "Expected a return value of type Int but got Bool");
    });

    it("should check type alias ifs", function () {
        checkTestFunctionInFile("type Foo = Bool; function main(): Int { if(true<Foo>) { return 3i; } return 1i; }");

        checkTestFunctionInFileError("type Foo = Int; function main(): Int { if(3i<Foo>) { return 3i; } return 1i; }", 'Guard expression does not evaluate to boolean');
    });
});
