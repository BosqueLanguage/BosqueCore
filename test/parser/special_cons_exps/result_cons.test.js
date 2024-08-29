"use strict";

import { parseTestExp } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Special Constructor", () => {
    it("should parse ok/fail", function () {
        parseTestExp("ok(3i)", undefined, "Result<Int, Bool>");
        parseTestExp("fail('bad name')", undefined, "Result<Int, CString>");
    });
});
