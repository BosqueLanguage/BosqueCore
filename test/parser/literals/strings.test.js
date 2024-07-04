"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- String", () => {
    it("should parse simple strings", function () {
        parseTestExp('""', undefined, "String");
        parseTestExp('"abc"', undefined, "String");
        parseTestExp('"a🌵c"', undefined, "String");
    });

    it("should parse escaped strings", function () {
        parseTestExp('"%x59;"', undefined, "String");
        parseTestExp('"%x1f335;"', undefined, "String");
        parseTestExp('"%%;"', undefined, "String");
        parseTestExp('"%;"', undefined, "String");
    });

    it("should fail missing quotes", function () {
        parseTestExpError('"abc', "Unterminated string literal", "String");
    });
});

describe ("Parser -- CString", () => {
    it("should parse simple cstrings", function () {
        parseTestExp("''", undefined, "CString");
        parseTestExp("'abc'", undefined, "CString");
    });

    it("should parse escaped strings", function () {
        parseTestExp("'%x59;'", undefined, "CString");
        parseTestExp("'%%;'", undefined, "CString");
        parseTestExp("'%;'", undefined, "CString");
    });

    it("should fail missing quotes", function () {
        parseTestExpError("'abc", "Unterminated CString literal", "CString");
    });
    it("should fail illegal chars", function () {
        parseTestExpError("'a🌵c'", "Invalid chacaters in CString literal", "CString");
        parseTestExpError("'\v'", "err4", "CString");
    });
});