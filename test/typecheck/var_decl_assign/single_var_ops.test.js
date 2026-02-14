"use strict";

import { checkTestFunction, checkTestFunctionError, checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- simple declare only", () => {
    it("should type simple declares", function () {
        checkTestFunction("function main(): Int { var x: Int; return 0i; }");
        checkTestFunction("function main(): Bool { var x: Bool; return true; }");
    });

    it("should fail simple use of undefined", function () {
        checkTestFunctionError("function main(): Int { var x: Int; return x; }", "Variable x may not be defined on all control flow paths");
    });
});

describe ("Checker -- simple declare-assign only", () => {
    it("should type simple declare-assign", function () {
        checkTestFunction("function main(): Int { var x: Int = 5i; return x; }");
        checkTestFunction("function main(): Int { ref x: Int = 5i; return x; }");
        checkTestFunction("function main(): Bool { let x: Bool = true; return x; }");
    });

    it("should type simple declare-assign infer type", function () {
        checkTestFunction("function main(): Int { var x = 5i; return x; }");
        checkTestFunction("function main(): Int { ref x = 5i; return x; }");
        checkTestFunction("function main(): Bool { let x = true; return x; }");
    });

    it("should fail simple wrong result type", function () {
        checkTestFunctionError("function main(): Bool { let x: Bool = 5i; return x; }", "Expression of type Int cannot be assigned to variable of type Bool");
    });

    it("should check simple declare-assign with coerce", function () {
        checkTestFunctionInFile('function main(): Option<Int> { let x: Option<Int> = none; return x; }');
        checkTestFunctionInFile('function main(): Option<Int> { let x: Option<Int> = some(3i); return x; }');
        checkTestFunctionInFile('function main(): Option<Int> { ref x: Option<Int> = some(3i); return x; }');

        checkTestFunctionInFile('concept Baz {} entity Foo provides Baz {} function main(): Baz { let x: Baz = Foo{}; return x; }');
        checkTestFunctionInFile('concept Baz {} entity Foo provides Baz {} function main(): Baz { var x: Baz = Foo{}; return x; }');
    });

    it("should check fail simple declare-assign with coerce", function () {
        checkTestFunctionInFileError('function main(): Int { ref x: Option<Int> = some(3n); return 1i; }', "Some constructor argument is not a subtype of Int");

        checkTestFunctionInFileError('concept Baz {} entity Foo {} function main(): Int { let x: Baz = Foo{}; return 3i; }', "Expression of type Foo cannot be assigned to variable of type Baz");
    });
});

describe ("Checker -- simple assign", () => {
    it("should type simple assign", function () {
        checkTestFunction("function main(): Int { var x: Int = 5i; x = 2i; return x; }");
        checkTestFunction("function main(): Int { var x: Int = 5i; x = 2i; x = 0i; return x; }");
    });

    it("should ignore assign", function () {
        checkTestFunction("function main(): Int { _ = 2i; return 0i; }");
    });

    it("should fail simple wrong assign type", function () {
        checkTestFunctionError("function main(): Int { var x = 5i; x = true; return x; }", "Expression of type Bool cannot be assigned to variable of type Int");
    });

    it("should check simple assign with coerce", function () {
        checkTestFunctionInFile('function main(): Option<Int> { var x: Option<Int> = none; x = some(3i); return x; }');

        checkTestFunctionInFile('concept Baz {} entity Foo provides Baz {} function main(): Baz { var x: Baz = Foo{}; x = Foo{}; return x; }');
    });
});
