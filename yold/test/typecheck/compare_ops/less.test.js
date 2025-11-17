"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- basic <", () => {
    it("should check compare simple types", function () {
        checkTestExp("0n < 1n", "Bool");
        checkTestExp("+2i < -2i", "Bool");
        checkTestExp("+2.0f < 1.0f", "Bool");
        checkTestExp("+2/3R < 1/3R", "Bool");
    });

    it("should fail not same type", function () {
        checkTestExpError("0n < 5i", "Bool", "Operator < requires 2 arguments of the same type");
    });

    it("should fail not numeric", function () {
        checkTestExpError("none < true", "Bool", "Binary operator requires a unique numeric type");
    });
});

describe ("Checker -- basic <=", () => {
    it("should check compare simple types", function () {
        checkTestExp("0n <= 1n", "Bool");
        checkTestExp("+2i <= -2i", "Bool");
        checkTestExp("+2.0f <= 1.0f", "Bool");
        checkTestExp("+2/3R <= 1/3R", "Bool");
    });

    it("should fail not same type", function () {
        checkTestExpError("0n <= 5i", "Bool", "Operator <= requires 2 arguments of the same type");
    });

    it("should fail not numeric", function () {
        checkTestExpError("none <= true", "Bool", "Binary operator requires a unique numeric type");
    });
});
