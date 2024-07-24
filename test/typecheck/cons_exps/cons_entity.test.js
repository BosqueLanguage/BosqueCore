"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Entity Constructor", () => {
    it("should check positional", function () {
        checkTestFunctionInFile('entity Foo { } function main(): Foo { return Foo{}; }');
        checkTestFunctionInFile('entity Foo { field f: Int; } function main(): Foo { return Foo{1i}; }');
        checkTestFunctionInFile('entity Foo { field f: Int; field g: Bool; } function main(): Foo { return Foo{1i, false}; }');
    });

    it("should check nominal", function () {
        checkTestFunctionInFile('entity Foo { field f: Int; } function main(): Foo { return Foo{f=1i}; }');
        checkTestFunctionInFile('entity Foo { field f: Int; field g: Bool; } function main(): Foo { return Foo{g=true, 1i}; }');
    });

    it("should check default", function () {
        checkTestFunctionInFile('entity Foo { field f: Int = 0i; } function main(): Foo { return Foo{}; }');
        checkTestFunctionInFile('entity Foo { field f: Int = 0i; field g: Bool; } function main(): Foo { return Foo{g=true}; }');
    });

    it("should fail positional", function () {
        checkTestFunctionInFileError('entity Foo { field f: Int; } function main(): Foo { return Foo{}; }', 'Required argument f not provided');
    });

    it("should fail default", function () {
        checkTestFunctionInFileError('entity Foo { field f: Int = 0n; } function main(): Foo { return Foo{}; }', 'Field initializer does not match declared type -- expected Int but got Nat');
        checkTestFunctionInFileError('entity Foo { field f: Int = 0i; field g: Bool; } function main(): Foo { return Foo{true}; }', 'Argument f expected type Int but got Bool');
        checkTestFunctionInFileError('entity Foo { field f: Int = 0i; field g: Bool; } function main(): Foo { return Foo{true, false}; }', 'Argument f expected type Int but got Bool');
    });
});
