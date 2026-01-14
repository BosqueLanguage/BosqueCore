"use strict";

import { checkTestExp, checkTestExpError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple numeric sign", () => {
    it("should check simple sign", function () {
        checkTestExp("-(3i)", "Int");
        checkTestExp("+(5n)", "Nat");
        checkTestExp("-(+0.0f)", "Float");
    });

    it("should fail sign type", function () {
        checkTestExpError("-(3i)", "ChkInt", "Expected a return value of type ChkInt but got Int");
    });

    it("should fail paren sign type", function () {
        checkTestExpError("+(5I)", "Float", "Expected a return value of type Float but got ChkInt");
    });

    it("should check typedecl sign", function () {
        checkTestFunctionInFile("type Foo = Int; function main(): Foo { return +(5i<Foo>); }");
        checkTestFunctionInFile("type Foo = Int; function main(): Foo { return -(3i<Foo>); }");
    });

    it("should fail typedecl sign invalid", function () {
        checkTestFunctionInFileError("type IsFooEnabled = Bool; function main(): IsFooEnabled { return -(true<IsFooEnabled>); }", "Prefix Negate/Plus operator requires a unique numeric type");
    });
});
