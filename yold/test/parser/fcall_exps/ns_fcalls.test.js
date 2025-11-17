"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError, parseTestFunctionInFilePlus, parseTestFunctionInFilePlusError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- NamespaceFunction Implicit (no template)", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('function foo(): Int { return 1i; } [FUNC]', 'function main(): Int { return foo(); }');
        parseTestFunctionInFile('function foo(x: Int, y: Int): Int { return x + y; } [FUNC]', 'function main(): Int { return foo(1i, 2i); }');    
    });

    it("should parse named", function () {
        parseTestFunctionInFile('function foo(x: Int, y: Int): Int { return x + y; } [FUNC]', 'function main(): Int { return foo(x = 1i, y = 2i); }');
        parseTestFunctionInFile('function foo(x: Int, y: Int): Int { return x + y; } [FUNC]', 'function main(): Int { return foo(y = 1i, x = 2i); }');
        parseTestFunctionInFile('function foo(x: Int, y: Int): Int { return x + y; } [FUNC]', 'function main(): Int { var x: Int = 0i; return foo(y = x, x = x); }');
    });

    it("should parse mixed", function () {
        parseTestFunctionInFile('function foo(x: Int, y: Int): Int { return x + y; } [FUNC]', 'function main(): Int { return foo(x = 1i, 2i); }');
        parseTestFunctionInFile('function foo(x: Int, y: Int): Int { return x + y; } [FUNC]', 'function main(): Int { return foo(y = 1i, 2i); }');
        parseTestFunctionInFile('function foo(x: Int, y: Int): Int { return x + y; } [FUNC]', 'function main(): Int { return foo(1i, x = 2i); }');
    });

    it("should parse rest", function () {
        parseTestFunctionInFile('function foo(x: Int, ...y: List<Int>): Int { return x; } [FUNC]', 'function main(): Int { return foo(1i); }');
        parseTestFunctionInFile('function foo(x: Int, ...y: List<Int>): Int { return x; } [FUNC]', 'function main(): Int { return foo(1i, 2i); }');
        parseTestFunctionInFile('function foo(x: Int, ...y: List<Int>): Int { return x; } [FUNC]', 'function main(): Int { return foo(1i, 2i, 3i); }');
        parseTestFunctionInFile('function foo(x: Int, ...y: List<Int>): Int { return x; } [FUNC]', 'function main(): Int { return foo(3i, x = 1i); }');
        
    });

    it("should parse ref", function () {
        parseTestFunctionInFile('function foo(ref x: Int): Int { return 1i; } [FUNC]', 'function main(): Int { var y: Int = 0i; return foo(ref y); }');
    });

    it("should parse default", function () {
        parseTestFunctionInFile('function foo(x: Int = 3i, y: Int = $x + 1i): Int { return x + y; } [FUNC]', 'function main(): Int { return foo(1i, 2i); }');
        parseTestFunctionInFile('function foo(x: Int = 3i, y: Int = $x + 1i): Int { return x + y; } [FUNC]', 'function main(): Int { return foo(1i); }');    
    });

    it("should fail positional", function () {
        parseTestFunctionInFileError('function foo(x: Int, y: Int): Int { return x + y; } function main(): Int { return foo(1i 2i); ', 'Expected ")" but got "[RECOVER]" when parsing "argument list"');
        parseTestFunctionInFileError('function foo(x: Int, y: Int): Int { return x + y; } function main(): Int { return foo(, 2i); ', 'Unexpected token in expression -- ,');
        parseTestFunctionInFileError('function foo(x: Int, y: Int): Int { return x + y; } function main(): Int { return foo(1i, 2i,,); ', 'Unexpected token in expression -- ,');

        parseTestFunctionInFileError('function foo(x: Int, y: Int): Int { return x + y; } function main(): Int { return foo(1i, 2, 3i); ', 'Un-annotated numeric literals are not supported');
    });

    it("should fail named", function () {
        parseTestFunctionInFileError('function foo(x: Int, y: Int): Int { return x + y; } function main(): Int { return foo(x = 1i y = 2i); ', 'Expected ")" but got "[RECOVER]" when parsing "argument list"');
        parseTestFunctionInFileError('function foo(x: Int, y: Int): Int { return x + y; } function main(): Int { return foo(x 1i, 2i); ', "Could not resolve 'x' in this context");
    });

    it("should fail rest", function () {
        parseTestFunctionInFileError('function foo(...x: List<Int>, y: Int): Int { return x + y; } function main(): Int { return foo(1i, 2i); ', 'Rest parameter must be the last parameter');
        parseTestFunctionInFileError('function foo(x: Int, y: Int): Int { return x + y; } function main(): Int { return foo(x 1i, 2i); ', "Could not resolve 'x' in this context");
    });

    it("should fail ref", function () {
        parseTestFunctionInFileError('function foo(ref ...x: List<Int>): Int { return x + y; } function main(): Int { return foo(1i, 2i); ', 'Cannot have a parameter that is both a reference and a rest');
        parseTestFunctionInFileError('function foo(ref x: Int): Int { return 1i; } function main(): Int { var y: Int = 0i; return foo(ref x = y); }', "Could not resolve 'x' in this context");
    });

    it("should fail default", function () {
        parseTestFunctionInFileError('function foo(x: Int 1i, y: Int): Int { return x + y; } function main(): Int { return foo(1i 2i); ', 'Expected ")" but got "[RECOVER]" when parsing "function parameter list"');
        parseTestFunctionInFileError('function foo(x: Int =, y: Int): Int { return x + y; } function main(): Int { return foo(, 2i); ', 'Unexpected token in expression -- ,');
    });
});

const ctxcode = [
    'declare namespace NSOther; function foo(x: Int): Int { return x; }'
];

describe ("Parser -- NamespaceFunction explicit (no template)", () => {
    it("should parse explicit Same access", function () {
        parseTestFunctionInFile("function foo(x: Int): Int { return x; } [FUNC]", 'function main(x: Int): Int { return Main::foo(x); }'); 
    });

    it("should parse explicit Other access", function () {
        parseTestFunctionInFilePlus("declare namespace Main { using NSOther; } [FUNC]", 'function main(x: Int): Int { return NSOther::foo(x); }', undefined, ...ctxcode);  //Core is always ok
    });

    it("should fail undefined namespace", function () {
        parseTestFunctionInFilePlusError('declare namespace Main; function main(x: Int): Int { return Other::foo(x); }', "Unknown namespace Other", ...ctxcode);  //NS does not exist
    });

    it("should fail not-imported namespace", function () {
        parseTestFunctionInFilePlusError('declare namespace Main; function main(x: Int): Int { return NSOther::foo(x); }', "Missing import for namespace NSOther", ...ctxcode);  //NS exists but not imported
    });
});

describe ("Parser -- NamespaceFunction Implicit (with template)", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('function foo<T>(x: T): Int { return x; } [FUNC]', 'function main(): Int { return foo<Int>(3i); }'); 
    });
});
