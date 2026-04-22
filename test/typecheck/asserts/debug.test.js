"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple Debug", () => {
    it("should check debug", function () {
        checkTestFunction("function main(): Int { _debug 3i; return 1i; }");
    });
});
