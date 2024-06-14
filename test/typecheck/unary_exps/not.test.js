"use strict";

import { checkTestExp, checkTestExpError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple Boolean not", () => {
    it("should check simple not", function () {
        checkTestExp("!false", "Bool");
        checkTestExp("!!true", "Bool");
    });

    it("should fail not boolean type", function () {
        checkTestExpError("!none", "Bool", "Prefix Not operator requires a Bool type");
    });

    it("should fail paren not boolean type", function () {
        checkTestExpError("!(5i)", "Bool", "Prefix Not operator requires a Bool type");
    });
});