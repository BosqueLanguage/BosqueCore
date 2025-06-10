"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Check -- op and", () => {
    it("should check simple and", function () {
        checkTestExp("/\\(true)", "Bool");
        checkTestExp("/\\(true, false)", "Bool");
        checkTestExp("/\\(true, false, false)", "Bool");
    });

    it("should check bad type", function () {
        checkTestExpError("/\\(true, 5i)", "Bool", "And subexpression 1 is not a subtype of Bool");
        checkTestExpError("/\\(true, false)", "None", "Expected a return value of type None but got Bool");
    });
});
