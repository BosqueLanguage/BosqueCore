"use strict";

import { checkTestExp } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("TypeChecker -- special literals", () => {
    it("should check none", () => {
        checkTestExp("none", "None");
    });

    it("should check true", function () {
        checkTestExp("true", "Bool");
    });

    it("should check false", function () {
        checkTestExp("false", "Bool");
    });
});
