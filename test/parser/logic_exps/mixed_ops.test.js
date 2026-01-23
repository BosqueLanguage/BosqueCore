"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- logical mixed", () => {
    it("should parse implicit", function () {
        parseTestExp("true || false && true", "true || (false && true)", "Bool");
        parseTestExp("true && false || true", "(true && false) || true", "Bool");
    });

    it("should parse explicit", function () {
        parseTestExp("(true || false) && true", "(true || false) && true", "Bool");
        parseTestExp("true && (false || true)", "true && (false || true)", "Bool");
    });
});