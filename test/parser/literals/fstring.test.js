"use strict";

import { parseTestExp } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- FCString", () => {
    it("should parse simple fcstrings", function () {
        parseTestExp("$'${1}'", undefined, "FCString<CString, CString>");
        parseTestExp("$'ok ${arg}'", undefined, "FCString<CString, arg: CString>");
        parseTestExp("$'${1}-${1}'", undefined, "FCString<CString, CString>");
        parseTestExp("$'${1}-${2}'", undefined, "FCString<CString, CString, CString>");
        parseTestExp("$'${1: CString}-${1}'", undefined, "FCString<CString, CString>");
        parseTestExp("$'ok ${arg: CString}'", undefined, "FCString<CString, arg: CString>");
    });
});

