"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- interpolate cstring", () => {
    it("should check simple interpolate cstring", function () {
        checkTestExp("Interpolate::cstring($'-${0}-', 'a')", "CString");
        //checkTestExp("Interpolate::cstring($'${0}-${1}', 'a', 'b')", "CString");

        //checkTestExp("Interpolate::cstring<CString>($'${0}-${1}', 'a', 'b')", "CString");
    });

    it("should fail bad index/names", function () {
        checkTestExpError("Interpolate::cstring($'${1}', 'aa')", "CString", "aaa");
        //checkTestExpError("Interpolate::cstring($'${-1}', 'aa')", "CString", "bbb");

        //checkTestExpError("Interpolate::cstring($'${0}', val = 'aa')", "CString", "ddd");

        //checkTestExpError("Interpolate::cstring($'${arg: y}', 'aa')", "CString", "ccc");
        //checkTestExpError("Interpolate::cstring($'${arg: y}', val = 'aa')", "CString", "ccc");
    });
});

