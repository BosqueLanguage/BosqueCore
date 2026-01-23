"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- logical mixed", () => {
    it("should check implicit", function () {
        checkTestExp("true || false && true", "Bool");
        checkTestExp("true && false || true", "Bool");
    });

    it("should check explicit", function () {
        checkTestExp("(true || false) && true", "Bool");
        checkTestExp("true && (false || true)", "Bool");
    });
});