"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- NamespaceFunction Ref Params", () => {
    it("should check simple ref", function () {
        checkTestFunctionInFile('function foo(out y: Int): Int { y = 2i; return 1i; } function main(): Int { var i = 0i; return foo(out i); }');
        checkTestFunctionInFile('function foo(out? y: Int): Bool { y = 2i; return true; } function main(): Bool { var i = 0i; return foo(out? i); }');
        checkTestFunctionInFile('function foo(inout y: Int): Int { y = y + 2i; return 1i; } function main(): Int { var i = 0i; return foo(inout i); }');
        checkTestFunctionInFile('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { ref ff = Foo{}; return foo(ref ff); }');     
    });

    it("should check fail simple passing", function () {
        checkTestFunctionInFileError('function foo(out? y: Int): Int { y = 2i; return 1i; } function main(): Int { var i = 0i; return foo(out? i); }', 'Function with conditional out parameter y must have a boolean return type');

        checkTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { var v = Foo{}; return foo(v); }', 'Could not find namespace function Main::foo');
        checkTestFunctionInFileError('entity Foo{ } function foo(y: Foo): Int { return 1i; } function main(): Int { var v = Foo{}; return foo(ref v); }', 'Could not find namespace function Main::foo');

        checkTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { let v = Foo{}; return foo(ref v); }', 'Variable v cannot be passed as ref');
        checkTestFunctionInFileError('function foo(out y: Int): Int { y = 3i; return 1i; } function main(): Int { let v = 0i; return foo(out v); }', 'Variable v cannot be passed as out');

        checkTestFunctionInFileError('function foo(out y: Int): Int { y = 3i; return 1i; } function main(): Int { let v = 0i; return foo(inout v); }', 'Parameter y passing kind does not match the passing kind of the argument');
        checkTestFunctionInFileError('function foo(out y: Int): Int { y = 3i; return 1i; } function main(): Int { let v = 0i; return foo(ref v); }', 'Parameter y passing kind does not match the passing kind of the argument');

        checkTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { let v = Foo{}; return foo(out v); }', 'Parameter y passing kind does not match the passing kind of the argument');
        checkTestFunctionInFileError('function foo(ref y: Int): Int { return 1i; } function main(): Int { let v = 0i; return foo(ref v); }', 'Ref parameter must be of an updatable type');
    });
});
