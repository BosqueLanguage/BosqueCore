"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it, run } from "node:test";


describe ("Exec -- Lambda calls (no template)", () => {
    it("should exec simple lambda", function () {
        runMainCode("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { return foo(fn(x) => { return x + 1i; }); }", [2n, "Int"]);
    
        runMainCode("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { let y = 1i; return foo(fn(x) => { return x + y; }); }", [2n, "Int"]);

        runMainCode('function foo(f: fn(Int) -> Int): Int { return f(1i); } function bar(g: fn(Int) -> Int, k: Int): Int { return foo(fn(y) => g(y) + k); } public function main(): Int { let y = 1i; return bar(fn(x) => { return x + y; }, 2i); }', [4n, "Int"]);
    });
});

describe ("Exec -- Lambda calls (with template)", () => {
    it("should exec simple lambda template", function () {
        runMainCode("function foo<T>(x: T, f: fn(T) -> T): T { return f(x); } public function main(): Int { return foo<Int>(3i, fn(x) => x); }", [3n, "Int"]);
    });
});
