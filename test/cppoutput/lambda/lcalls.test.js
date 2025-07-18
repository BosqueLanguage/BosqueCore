"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Lambda calls (no template)", () => {
    it("should exec simple lambda", function () {
        runMainCode("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { return foo(fn(x) => { return x + 1i; }); }", "2_i");
    
        runMainCode("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { let y = 1i; return foo(fn(x) => { return x + y; }); }", "2_i");

        runMainCode('function foo(f: fn(Int) -> Int): Int { return f(1i); } function bar(g: fn(Int) -> Int, k: Int): Int { return foo(fn(y) => g(y) + k); } public function main(): Int { let y = 1i; return bar(fn(x) => { return x + y; }, 2i); }', "4_i");
    });
});

describe ("CPP Emit Evaluate -- Lambda calls (with template)", () => {
    it("should exec simple lambda template", function () {
        runMainCode("function foo<T>(x: T, f: fn(T) -> T): T { return f(x); } public function main(): Int { return foo<Int>(3i, fn(x) => x); }", "3_i");
    });
});
