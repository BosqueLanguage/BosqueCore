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
        checkTestExpError("/\\(true, 5i)", "Bool", "and_err1");
        checkTestExpError("/\\(true, false)", "None", "and_err2");
    });
});
