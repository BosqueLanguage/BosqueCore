"use strict";

import { checkTestFunctionInFile } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Lambda calls (no template)", () => {
    it("should check lambda capture", function () {
        checkTestFunctionInFile("function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(): Int { let y = 1i; return foo(fn(x) => { return x + y; }); }");

        checkTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } function bar(g: fn(Int) -> Int, k: Int): Int { return foo(fn(y) => g(y) + k); } public function main(): Int { let y = 1i; return bar(fn(x) => { return x + y; }, 2i); }');

        checkTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(g: fn(Int) -> Int): Int { let y = 1i; return foo(g); }');
        checkTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } function main(g: fn(Int) -> Int): Int { let y = 1i; return foo(fn(x) => { return g(x) + y; }); }');
    });
});

