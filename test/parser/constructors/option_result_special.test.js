"use strict";

import { parseTestFunction, parseTestExp } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Special Constructor Option", () => {
    it("should parse none/some", function () {
        parseTestExp("none", undefined, "None");
        parseTestExp("some(3i)", undefined, "Some<Int>");
    });

    it("should parse nested option return", function () {
        parseTestFunction("function main(x: None): Option<Option<Int>> { return x; }");
        parseTestFunction("function main(x: Some<Int>): Option<Option<Int>> { return some(x); }");
        parseTestFunction("function main(x: Option<Int>): Option<Option<Int>> { return some(x); }");
    });
});

