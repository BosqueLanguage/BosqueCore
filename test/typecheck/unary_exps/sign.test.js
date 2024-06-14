"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple Boolean not", () => {
    it("should check simple not", function () {
        checkTestExp("-(3i)", "Int");
        checkTestExp("+(5n)", "Nat");
        checkTestExp("-(+0.0f)", "Float");
    });

    it("should fail not boolean type", function () {
        checkTestExpError("-(3i)", "BigInt", "Expected a return value of type BigInt but got Int");
    });

    it("should fail paren not boolean type", function () {
        checkTestExpError("+(5.0d)", "Float", "Expected a return value of type Float but got Decimal");
    });
});