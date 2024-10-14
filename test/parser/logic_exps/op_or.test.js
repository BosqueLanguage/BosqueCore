"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- op or", () => {
    it("should parse simple or", function () {
        parseTestExp("\\/(true)", undefined, "Bool");
        parseTestExp("\\/(true, false)", undefined, "Bool");
        parseTestExp("\\/(true, false, false)", undefined, "Bool");
    });

    it("should fail empty", function () {
        parseTestExpError("\\/()", "empty logical or-expression is not allowed", "Bool");
    });
});
