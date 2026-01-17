"use strict";

import { parseTestExp } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Special Constructor Option", () => {
    it("should parse none/some", function () {
        parseTestExp("none", undefined, "None");
        parseTestExp("some(3i)", undefined, "Some<Int>");
    });
});

