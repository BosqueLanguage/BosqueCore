"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- NamespaceFunction Ref Params", () => {
    it("should check simple ref", function () {
        checkTestFunctionInFile('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } public function main(): Int { var ff = Foo{}; return foo(ref ff); }');    
    });

    it("should check fail simple ref", function () {
        checkTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { var v = Foo{}; return foo(v); }', 'Parameter y is a reference parameter and must be passed by reference');
        checkTestFunctionInFileError('entity Foo{ } function foo(y: Foo): Int { return 1i; } function main(): Int { var v = Foo{}; return foo(ref v); }', 'Parameter y is not a reference parameter and argument cannot be passed by reference');

        checkTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { let v = Foo{}; return foo(ref v); }', 'Variable v is cannot be updated (is local const or not a ref param)');
    });
});

