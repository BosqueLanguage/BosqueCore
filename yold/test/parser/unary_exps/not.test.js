"use strict";

import { parseTestExp } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Boolean not", () => {
    it("should parse simple not", function () {
        parseTestExp("!true", undefined, "Bool");
        parseTestExp("!!true", "!(!true)", "Bool");
    });
});

