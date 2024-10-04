"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- simple return", () => {
    it("should check simple returns", function () {
        checkTestFunction('function main(): Int { return 2i; }');
    });

    it("should check fail simple returns", function () {
        checkTestFunctionError('function main(): Int { return true; }', "Expected a return value of type Int but got Bool");
    });
});
