"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError, } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Lambda calls", () => {
    it("should parse simple capture", function () {
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(): Bool { let y = 1i; return foo(fn(x) => { return x + y; }); }');

        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(g: fn(Int) -> Int): Bool { let y = 1i; return foo(g); }');
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } [FUNC]', 'function main(g: fn(Int) -> Int): Bool { let y = 1i; return foo(fn(x) => { return g(x) + y; }); }');
    });

    it("should parse simple capture fail", function () {
        parseTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Bool { let y = 1i; return foo(fn(x) => { return x + z; }); }', "Could not resolve 'z' in this context");
    });
});