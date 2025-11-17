"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- logical implies", () => {
    it("should check simple implies", function () {
        checkTestExp("true ==> false", "Bool");
    });

    it("should fail wrong type", function () {
        checkTestExpError("true ==> 3i", "Bool", "Binary operator requires a Bool type");
    });
});
