"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- String", () => {
    it("should check simple strings", function () {
        checkTestExp('""', "String");
        checkTestExp('"abc"', "String");
        checkTestExp('"a🌵c"', "String");
    });

    it("should check escaped strings", function () {
        checkTestExp('"%x59;"', "String");
        checkTestExp('"%x1f335;"', "String");
        checkTestExp('"%%;"', "String");
        checkTestExp('"%;"', "String");
    });

    it("should fail bad escapes", function () {
        checkTestExpError('"a%53"', "String", "Escape sequence is missing terminal ';'");
        checkTestExpError('"a%bob;"', "String", "err3");
    });
});

describe ("Checker -- CString", () => {
    it("should check simple cstrings", function () {
        checkTestExp("''", "CString");
        checkTestExp("'abc'", "CString");
        
    });

    it("should check escaped strings", function () {
        checkTestExp("'%x59;'", "CString");
        checkTestExp("'%%;'", "CString");
        checkTestExp("'%;'", "CString");
    });

    it("should fail bad escapes", function () {
        checkTestExpError("'a%53'", "CString", "Escape sequence is missing terminal ';'",);
        checkTestExpError("'a%bob;'", "CString", "Invalid escape sequence -- unknown escape name 'bob'");

        checkTestExpError("'%x1f335;'", "CString", "err5");
    });
});
