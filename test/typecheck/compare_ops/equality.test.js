"use strict";

import { checkTestExp, checkTestExpError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- basic equals", () => {
    it("should check compare simple types", function () {
        checkTestExp("0n == 1n", "Bool");
        checkTestExp("+2i == -2i", "Bool");
        checkTestExp("+2.0f == 1.0f", "Bool");
        checkTestExp("+2/3R == 1/3R", "Bool");
    });

    it("should fail not same type", function () {
        checkTestExpError("0n == 5i", "Bool", "Operator == requires 2 arguments of the same type");
    });

    it("should fail not numeric", function () {
        checkTestExpError("none == true", "Bool", "Binary operator requires a unique numeric type");
    });

    it("should check type alias", function () {
        checkTestFunctionInFile("type Foo = Int; function main(): Bool { return 5i<Foo> == 5i<Foo>; }");
    });

    it("should fail type alias", function () {
        checkTestFunctionInFileError("type Foo = Int; type Bar = Int; function main(): Bool { return 5i<Foo> == 5i<Bar>; }", "Operator == requires 2 arguments of the same type");
        checkTestFunctionInFileError("type Foo = Int; function main(): Bool { return 5i<Foo> == 5i; }", "Operator == requires 2 arguments of the same type");
    });
});

describe ("Checker -- basic !equal", () => {
    it("should check compare simple types", function () {
        checkTestExp("0n != 1n", "Bool");
        checkTestExp("+2i != -2i", "Bool");
        checkTestExp("+2.0f != 1.0f", "Bool");
        checkTestExp("+2/3R != 1/3R", "Bool");
    });

    it("should fail not same type", function () {
        checkTestExpError("0n == 5i", "Bool", "Operator == requires 2 arguments of the same type");
    });

    it("should fail not numeric", function () {
        checkTestExpError("none == true", "Bool", "Binary operator requires a unique numeric type");
    });

    it("should check type alias", function () {
        checkTestFunctionInFile("type Foo = Int; function main(): Bool { return 5i<Foo> != 5i<Foo>; }");
    });

    it("should fail type alias", function () {
        checkTestFunctionInFileError("type Foo = Int; type Bar = Int; function main(): Bool { return 5i<Foo> != 5i<Bar>; }", "Operator != requires 2 arguments of the same type");
        checkTestFunctionInFileError("type Foo = Int; function main(): Bool { return 5i<Foo> != 5i; }", "Operator != requires 2 arguments of the same type");
    });
});
