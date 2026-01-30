"use strict";

import { checkTestFunction, checkTestFunctionError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- simple return", () => {
    it("should check simple returns", function () {
        checkTestFunction('function main(): Int { return 2i; }');
    });

    it("should check fail simple returns", function () {
        checkTestFunctionError('function main(): Int { return true; }', "Expected a return value of type Int but got Bool");
    });

    it("should check simple returns with coerce", function () {
        checkTestFunctionInFile('function main(): Option<Int> { return none; }');
        checkTestFunctionInFile('function main(): Option<Int> { return some(3i); }');
        checkTestFunctionInFile('function main(): Option<Int> { let x: Option<Int> = some(3i); return x; }');

        checkTestFunctionInFile('concept Baz {} entity Foo provides Baz {} function main(): Baz { return Foo{}; }');
        checkTestFunctionInFile('concept Baz {} entity Foo provides Baz {} function main(): Baz { let x: Foo = Foo{}; return x; }');
    });

    it("should check fail simple returns with coerce", function () {
        checkTestFunctionInFileError('function main(): Int { return true; }', "Expected a return value of type Int but got Bool");
        checkTestFunctionInFileError('function main(): Option<Int> { return some(3n); }', "Some constructor argument is not a subtype of Int");

        checkTestFunctionInFileError('concept Baz {} entity Foo {} function main(): Baz { return Foo{}; }', "Expected a return value of type Baz but got Foo");
    });
});
