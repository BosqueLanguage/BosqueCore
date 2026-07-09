"use strict";

import { checkTestExp, checkTestExpError, checkTestFunctionInFile } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple Boolean not", () => {
    it("should check simple not", function () {
        checkTestExp("!false", "Bool");
        checkTestExp("!(!true)", "Bool");
    });

    it("should fail not boolean type", function () {
        checkTestExpError("!none", "Bool", "Expected a return value of type Bool but got None");
    });

    it("should fail paren not boolean type", function () {
        checkTestExpError("!(5i)", "Bool", "Expected a return value of type Bool but got Int");
    });

    it("should check typedecl not", function () {
        checkTestFunctionInFile("type IsFooEnabled = Bool; function main(): IsFooEnabled { return !true<IsFooEnabled>; }");
    });

    it("should fail typedecl not invalid", function () {
        checkTestFunctionInFile("type IsFooEnabled = Int; function main(): IsFooEnabled { return !5i<IsFooEnabled>; }", "Prefix Not operator requires a Bool based type");
    });
});
