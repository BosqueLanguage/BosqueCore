"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- logical and", () => {
    it("should check simple and", function () {
        checkTestExp("true && false", "Bool");
    });

    it("should fail wrong type", function () {
        checkTestExpError("true && 3i", "Bool", "One or more sub-expressions in 'and' expression is not a Bool compatible type");
    });
});
