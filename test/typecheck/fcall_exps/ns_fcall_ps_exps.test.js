"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- NamespaceFunction Ref Params", () => {
    it("should check simple ref", function () {
        checkTestFunctionInFile('function foo(out y: Int): Int { y = 2i; return 1i; } function main(): Int { var i = 0i; return foo(out i); }');
        checkTestFunctionInFile('function foo(out? y: Int): Bool { y = 2i; return true; } function main(): Bool { var i = 0i; return foo(out? i); }');
        checkTestFunctionInFile('function foo(inout y: Int): Int { y = y + 2i; return 1i; } function main(): Int { var i = 0i; return foo(inout i); }');
        //checkTestFunctionInFile('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { ref ff = Foo{}; return foo(ref ff); }');     
    });

    it("should check fail simple ref", function () {
        checkTestFunctionInFileError('function foo(out? y: Int): Int { y = 2i; return 1i; } function main(): Int { var i = 0i; return foo(out? i); }', 'Function with conditional out parameter y must have a boolean return type');

        /*
        checkTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { var v = Foo{}; return foo(v); }', 'Parameter y is a reference parameter and must be passed by reference');
        checkTestFunctionInFileError('entity Foo{ } function foo(y: Foo): Int { return 1i; } function main(): Int { var v = Foo{}; return foo(ref v); }', 'Parameter y is not a reference parameter and argument cannot be passed by reference');

        checkTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { let v = Foo{}; return foo(ref v); }', 'Variable v is cannot be updated (is local const or not a ref param)');
        */
    });
});
