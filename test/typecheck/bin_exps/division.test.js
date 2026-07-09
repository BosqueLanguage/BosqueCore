"use strict";

import { checkTestExp, checkTestExpError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Simple division", () => {
    it("should check simple ops", function () {
        checkTestExp("1n // 1n", "Nat");
        checkTestExp("+2i // -2i", "Int");
        checkTestExp("+2.0f // 1.0f", "Float");
    });

    it("should fail not same type", function () {
        checkTestExpError("0n // 5i", "Int", "Division operator requires 2 arguments of the same type");
    });

    it("should fail not numeric", function () {
        checkTestExpError("none // true", "Nat", "Binary operator requires a unique numeric type");
    });
        
    it("should check type alias ops", function () {
        checkTestFunctionInFile("type Foo = Int; function main(): Int { return 4i<Foo> // 2i<Foo>; }");
        checkTestFunctionInFile("type Foo = Int; function main(): Foo { return 6i<Foo> // 3i; }");
    });

    it("should fail type alias ops invalid", function () {
        checkTestFunctionInFileError("type Foo = Int; function main(): Foo { return 1n // 2n<Foo>; }", "Literal value is not the same type (Nat) as the value type (Int)");
        checkTestFunctionInFileError("type Foo = Int; function main(): Foo { return 1n<Foo> // 2i; }", "Literal value is not the same type (Nat) as the value type (Int)");
    });
});
