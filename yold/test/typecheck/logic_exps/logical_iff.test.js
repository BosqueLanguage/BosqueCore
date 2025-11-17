"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- logical iff", () => {
    it("should check simple iff", function () {
        checkTestExp("true <==> false", "Bool");
    });

    it("should fail wrong type", function () {
        checkTestExpError("none <==> 3i", "Bool", "Binary operator requires a Bool type");
    });
});
