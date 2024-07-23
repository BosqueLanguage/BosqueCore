"use strict";

import { parseTestExp } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Special Constructor Option", () => {
    it("should parse ok/err", function () {
        parseTestExp("ok(3i)", undefined, "Result<Int, Bool>");
        parseTestExp("err('bad name')", undefined, "Result<Int, CString>");
    });
});
