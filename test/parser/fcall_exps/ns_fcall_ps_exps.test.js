"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- NamespaceFunction Ref Params", () => {
    it("should parse simple passing", function () {
        parseTestFunctionInFile('function foo(out y: Int): Int { y = 2i; return 1i; } [FUNC]', 'function main(): Int { var i = 0i; return foo(out i); }');
        parseTestFunctionInFile('function foo(out? y: Int): Int { y = 2i; return 1i; } [FUNC]', 'function main(): Int { var i = 0i; return foo(out? i); }');
        parseTestFunctionInFile('function foo(inout y: Int): Int { y = y + 2i; return 1i; } [FUNC]', 'function main(): Int { var i = 0i; return foo(inout i); }');
        parseTestFunctionInFile('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } [FUNC]', 'function main(): Int { ref ff = Foo{}; return foo(ref ff); }');    
    });

    it("should parse fail simple passing", function () {
        parseTestFunctionInFileError('function foo(out y: Int): Int { y = 2i; return 1i; } function main(): Int { return foo(out 0i); }', "Expected variable as target in special passing argument");        
        parseTestFunctionInFileError('function foo(out? y: Int): Int { y = 2i; return 1i; } function main(): Int { return foo(out? 0i); }', "Expected variable as target in special passing argument");
        parseTestFunctionInFileError('function foo(inout y: Int): Int { y = y + 2i; return 1i; } function main(): Int { return foo(inout 0i); }', "Expected variable as target in special passing argument");
        parseTestFunctionInFileError('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } function main(): Int { return foo(ref Foo{}); }', "Expected variable as target in special passing argument");
    });
});
