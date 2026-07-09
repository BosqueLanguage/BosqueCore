"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- logical or", () => {
    it("should check simple or", function () {
        checkTestExp("true || false", "Bool");
    });

    it("should fail wrong type", function () {
        checkTestExpError("2i || true", "Bool", "Binary operator requires a Bool type");
    });
});
