"use strict";

import { checkTestExp, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- logical mixed", () => {
    it("should check implicit", function () {
        checkTestExp("true || false && true", "Bool");
        checkTestExp("true && false || true", "Bool");

        checkTestFunctionInFile("type Foo = Bool; const b: Foo = true<Foo>; public function main(): Foo { let z = true<Foo>; return z && Main::b; }");
        checkTestFunctionInFileError("type Foo = Bool; const b: Foo = true<Foo>; public function main(x: Bool): Bool { let z = true<Foo>; return z && x || Main::b; }", "Logic And expressions require all arguments to be of the same (Bool compatible) type");
    });

    it("should check explicit", function () {
        checkTestExp("(true || false) && true", "Bool");
        checkTestExp("true && (false || true)", "Bool");
    });
});