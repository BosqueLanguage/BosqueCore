"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Task Declarations", () => {
    it("should check simple task decl", function () {
        checkTestFunction('public task Main { field x: Int; action start(): APIResult<Int> { return success(1i); } }');
    });

    it("should check simple task decl fail", function () {
        checkTestFunctionError('public task Main { field x: Int; action start(): APIResult<Int> { return 1n; } }', 'Expected a return value of type APIResult<Int> but got Nat');
    });
});

describe ("Checker -- Task Calls", () => {
});
