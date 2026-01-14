"use strict";

import { parseTestExp, parseTestExpError, parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Nat division", () => {
    it("should parse simple ops", function () {
        parseTestExp("1n // 1n", undefined, "Nat");
        parseTestExp("2n // +2n", undefined, "Nat");
        parseTestExp("5n // 1n", undefined, "Nat");
    });

    it("should fail stuck signs", function () {
        parseTestExpError("2n//3n", 'Invalid characters in (or empty) Regex literal', "Nat");
    });

    it("should parse type alias ops", function () {
        parseTestFunctionInFile("type Foo = Int; [FUNC]", "function main(): Int { return 1i<Foo> // 2i<Foo>; }");
    });
});


describe ("Parser -- ChkInt division", () => {
    it("should parse simple chkint", function () {
        parseTestExp("0I // 1I", undefined, "ChkInt");
        parseTestExp("+2I // -2I", undefined, "ChkInt");
        parseTestExp("1I // +3I", undefined, "ChkInt");
    });

    it("should fail stuck signs", function () {
        parseTestExpError("2I//3I", 'Invalid characters in (or empty) Regex literal', "ChkInt");
    });
});
