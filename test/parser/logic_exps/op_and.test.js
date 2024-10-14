"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- op and", () => {
    it("should parse simple and", function () {
        parseTestExp("/\\(true)", undefined, "Bool");
        parseTestExp("/\\(true, false)", undefined, "Bool");
        parseTestExp("/\\(true, false, false)", undefined, "Bool");
    });

    it("should fail empty", function () {
        parseTestExpError("/\\()", "empty logical and-expression is not allowed", "Bool");
    });
});
