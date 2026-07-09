"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Int operation trees", () => {
    it("should parse simple pm", function () {
        parseTestExp("0i + 1i - 4i", "(0i + 1i) - 4i", "Int");
        parseTestExp("(+2n + 2n) - 2n", undefined, "Nat");
    });

    it("should parse precedence pm", function () {
        parseTestExp("0i + 1i * -4i", "0i + (1i * -4i)", "Int");
        parseTestExp("(0i + 1i) * -4i", undefined, "Int");
        parseTestExp("0i + (1i * -4i)", undefined, "Int");
        parseTestExp("+2n // 2n - 2n", "(+2n // 2n) - 2n", "Nat");
        parseTestExp("(+2n // 2n) - 2n", undefined, "Nat");
        parseTestExp("+2n // (2n - 2n)", undefined, "Nat");
    });
});