"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Check -- op or", () => {
    it("should check simple or", function () {
        checkTestExp("\\/(true)", "Bool");
        checkTestExp("\\/(true, false)", "Bool");
        checkTestExp("\\/(true, false, false)", "Bool");
    });

    it("should fail bad type", function () {
        checkTestExpError("\\/(false, 5i)", "Bool", "Or expression is not a subtype of Bool");
        checkTestExpError("\\/(true)", "Int", "Expected a return value of type Int but got Bool");
    });
});
