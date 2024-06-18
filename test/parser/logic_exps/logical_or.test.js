"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- logical or", () => {
    it("should parse simple or", function () {
        parseTestExp("true || false", undefined, "Bool");
    });

    it("should fail dangling", function () {
        parseTestExpError("true || ", "Unexpected token in expression -- ;", "Bool");
    });
});
