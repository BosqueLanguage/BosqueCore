"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- NamespaceFunction Ref Params", () => {
    it("should parse simple ref", function () {
        parseTestFunctionInFile('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } [FUNC]', 'function main(): Int { let ff = Foo{}; return foo(ref ff); }');    
    });

    it("should parse fail simple ref", function () {
        parseTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { return foo(ref Foo{}); }', "Expected variable as target in ref argument");
        parseTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { let ff = Foo{}; return foo(ff); }', "error2");
    });
});

