"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple subtraction", () => {
    it("should check simple nats", function () {
        checkTestExp("1n - 1n", "Nat");
        checkTestExp("+2i - -2i", "Int");
        checkTestExp("+2.0f - 1.0f", "Float");
        checkTestExp("+2/3R - 1/3R", "Rational");
    });

    it("should fail not same type", function () {
        checkTestExpError("0n - 5i", "Int", "Subtraction operator requires 2 arguments of the same type");
    });

    it("should fail not numeric", function () {
        checkTestExpError("none - true", "Nat", "Binary operator requires a unique numeric type");
    });
});
