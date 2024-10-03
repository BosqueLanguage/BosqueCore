"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- basic strict equals", () => {
    it("should parse strict equals operations", function () {
        parseTestExp("0n === 1n", undefined, "Bool");
        parseTestExp("0n !== 1n", undefined, "Bool");
        parseTestExp("0n !== none", undefined, "Bool");
        parseTestExp("none !== 3n", undefined, "Bool");
        parseTestExp("none === none", undefined, "Bool");
    });

    it("should parse fail strict equals operations", function () {
        parseTestExpError("0n ==== 5n", 'Expected ";" but got "=" when parsing "line statement"', "Bool");
    });
});
