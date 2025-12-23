"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple multiplication", () => {
    it("should check simple ops", function () {
        checkTestExp("1n * 1n", "Nat");
        checkTestExp("+2i * -2i", "Int");
        checkTestExp("+2.0f * 1.0f", "Float");
    });

    it("should fail not same type", function () {
        checkTestExpError("0n * 5i", "Int", "Multiplication operator requires 2 arguments of the same type");
    });

    it("should fail not numeric", function () {
        checkTestExpError("none * true", "Nat", "Binary operator requires a unique numeric type");
    });
});
