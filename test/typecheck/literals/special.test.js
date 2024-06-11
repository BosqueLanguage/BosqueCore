"use strict";

import { checkTestExp } from "/home/mark/Code/BosqueCore/bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("TypeChecker -- special literals", () => {
    it("should check none", () => {
        checkTestExp("none", "None");
    });
    
    it("should check nothing", function () {
        checkTestExp("nothing", "Nothing");
    });

    it("should check true", function () {
        checkTestExp("true", "Bool");
    });

    it("should check false", function () {
        checkTestExp("false", "Bool");
    });
});
