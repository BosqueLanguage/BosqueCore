"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Int operation trees", () => {
    it("should check simple pm", function () {
        checkTestExp("0i + 1i - 4i", "Int");
        checkTestExp("(+2n + 2n) - 2n", "Nat");
    });

    it("should fail invalid mixed types", function () {
        checkTestExpError("0i + 1n - 4i", "Int", "Addition operator requires 2 arguments of the same type");
    });

    it("should check precedence pm", function () {
        checkTestExp("0i + 1i * -4i", "Int");
        checkTestExp("(0i + 1i) * -4i", "Int");
        checkTestExp("0i + (1i * -4i)", "Int");
        checkTestExp("+2n // 2n - 2n", "Nat");
        checkTestExp("(+2n // 2n) - 2n", "Nat");
        checkTestExp("+2n // (2n - 2n)", "Nat");
    });
});
