"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- interpolate cstring", () => {
    it("should check simple interpolate cstring", function () {
        checkTestExp("Interpolate::cstring($'-${0}-', 'a')", "CString");
        checkTestExp("Interpolate::cstring($'${0}-${1}', 'a', 'b')", "CString");

        checkTestExp("Interpolate::cstring<CString>($'${0}-${1}', 'a', 'b')", "CString");
    });

    it("should fail bad index/names", function () {
        checkTestExpError("Interpolate::cstring($'${1}', 'aa')", "CString", "If format string argument indexes are used, then they must start at 0 (unless being matched to an inferred type)");
        checkTestExpError("Interpolate::cstring($'${-1}', 'aa')", "CString", "InterpolateFormatExpression with named format parameters must have all named arguments");

        checkTestExpError("Interpolate::cstring($'${0}', val = 'aa')", "CString", "InterpolateFormatExpression with positional format parameters must have all positional arguments");
        checkTestExpError("Interpolate::cstring($'${arg}', val = 'aa')", "CString", "Interpolation argument val does not match any format parameter");
    });
});

