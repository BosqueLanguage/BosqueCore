"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError, parseTestFunctionInFilePlus, parseTestFunctionInFilePlusError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Lambda calls", () => {
    it("should parse simple full", function () {
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(): Bool { return foo(fn(x: Int): Int => x + 1i); }');
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(): Bool { return foo(fn(x: Int): Int => { return x + 1i; }); }');
    });

    it("should parse simple infer", function () {
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(): Bool { return foo(fn(x): Int => { return x + 1i; }); }');
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(): Bool { return foo(fn(x: Int) => { return x + 1i; }); }');
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(): Bool { return foo(fn(x) => { return x + 1i; }); }');
    });

    it("should parse simple capture", function () {
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(): Bool { let y = 1i; return foo(fn(x) => { return x + y; }); }');
    });

    it("should parse fails", function () {
        parseTestFunctionInFileError('function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Bool { return foo(fn(x: Int): Int { return x + 1i; }); }', 'Expected " => " but got "{" when parsing "lambda declaration"');
        parseTestFunctionInFileError('function foo(f: fn(Int): Int): Int { return f(1i); } function main(): Bool { return foo(fn(x: Int): Int => { return x + 1i; }); }', 'Expected " -> " but got ":" when parsing "lambda type reference"');
        
        parseTestFunctionInFileError('function foo(f: (Int) -> Int): Int { return f(1i); } function main(): Bool { return foo(fn(x: Int): Int => { return x + 1i; }); }', 'Expected ")" but got "[RECOVER]" when parsing "function parameter list"');
        parseTestFunctionInFileError('function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Bool { return foo((x: Int): Int => { return x + 1i; }); }', "Could not resolve 'x' in this context");
    });

    it("should parse simple capture fail", function () {
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Bool { let y = 1i; return foo(fn(x) => { return x + z; }); }', "Could not resolve 'z' in this context");
    });
});

