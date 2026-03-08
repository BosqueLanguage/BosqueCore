"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- FCString", () => {
    it("should parse simple fcstrings", function () {
        parseTestExp("$'${1}'", undefined, "FCString<CString, String>");
        parseTestExp("$'ok ${arg}'", undefined, "FCString<CString, arg: String>");
        parseTestExp("$'${1}-${1}'", undefined, "FCString<CString, String>");
        parseTestExp("$'${1}-${2}'", undefined, "FCString<CString, String, String>");
        parseTestExp("$'${1: CString}-${1}'", undefined, "FCString<CString, String>");
        parseTestExp("$'ok ${arg: CString}'", undefined, "FCString<CString, arg: CString>");
    });

    it("should fail missing brace", function () {
        parseTestExpError("$'${1}-${2'", "error", "FCString<CString, CString, CString>");
    });
});

