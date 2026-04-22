"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- interpolate cstring", () => {
    it("should parse simple interpolate cstring", function () {
        parseTestExp("Interpolate::cstring($'-${1}-', 'a')", undefined, "CString");
        parseTestExp("Interpolate::cstring($'${1}-${2}', 'a', 'b')", undefined, "CString");

        parseTestExp("Interpolate::cstring<CString>($'${1}-${2}', 'a', 'b')", undefined, "CString");
    });

    it("should fail empty", function () {
        parseTestExpError("Interpolate::cstring()", "Interpolate expects the format string as the first (positional) argument", "CString");
    });
});

