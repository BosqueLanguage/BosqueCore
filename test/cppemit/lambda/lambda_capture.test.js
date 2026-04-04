"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Lambda calls (no template)", () => {
    it("should emit lambda capture", function () {
        checkTestEmitMainFunction("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { let y = 1i; return foo(fn(x) => { return x + y; }); }", 'Int Mainᕒmain() { Int y = 1_i; return Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{y}); }');

        /*
        checkTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } function bar(g: fn(Int) -> Int, k: Int): Int { return foo(fn(y) => g(y) + k); } public function main(): Int { let y = 1i; return bar(fn(x) => { return x + y; }, 2i); }');

        checkTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(g: fn(Int) -> Int): Int { let y = 1i; return foo(g); }');
        checkTestFunctionInFile('function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(g: fn(Int) -> Int): Int { let y = 1i; return foo(fn(x) => { return g(x) + y; }); }');
        */
    });
});
