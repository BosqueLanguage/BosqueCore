"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- FCString", () => {
    it("should check simple fcstrings", function () {
        checkTestExp("$'${0}'", "FCString<CString, CString>");
        checkTestExp("$'${0}-${1}'", "FCString<CString, CString, CString>");
        checkTestExp("$'${0: CString}-${0}'", "FCString<CString, CString>");

        checkTestExp("$'ok ${arg}'", "FCString<CString, arg: CString>");
        checkTestExp("$'ok ${arg: CString}+${arg}'", "FCString<CString, arg: CString>");
    });

    it("should fail duplicate names/bad count", function () {
        checkTestExpError("$'${0}-${1}'", "FCString<CString, CString>", "Expected a return value of type FCString<CString, CString> but got FCString<CString, CString, CString>");
        checkTestExpError("$'${a}-${b}'", "FCString<CString, a: CString, a: CString>", "Expected a return value of type FCString<CString, a: CString, a: CString> but got FCString<CString, a: CString, b: CString>");
    });
});

