"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it, run } from "node:test";

describe ("SMT -- Lambda calls (no template)", () => {
    it("should smt exec simple lambda", function () {
        runishMainCodeUnsat("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { return foo(fn(x) => { return x + 1i; }); }", "(assert (not (= 2 Main@main)))");
        runishMainCodeUnsat("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { let y = 1i; return foo(fn(x) => { return x + y; }); }", "(assert (not (= 2 Main@main)))");
        runishMainCodeUnsat('function foo(f: fn(Int) -> Int): Int { return f(1i); } function bar(g: fn(Int) -> Int, k: Int): Int { return foo(fn(y) => g(y) + k); } public function main(): Int { let y = 1i; return bar(fn(x) => { return x + y; }, 2i); }', "(assert (not (= 4 Main@main)))");

        runishMainCodeUnsat('function foo(f: fn(Int) -> Int): Int { return f(1i); } function bar(g: fn(Int) -> Int, k: Int): Int { return foo(fn(y) => g(y) + k); } public function main(): Int { let y = 1i; return bar(fn(x) => { assert x != 0i; return x + y; }, 2i); }', "(assert (not (= (@Result-ok 4) Main@main)))");
        runishMainCodeUnsat('function foo(f: fn(Int) -> Int): Int { return f(1i); } function bar(g: fn(Int) -> Int, k: Int): Int { return foo(fn(y) => g(y) + k); } public function main(): Int { let y = 1i; return bar(fn(x) => { assert x != 1i; return x + y; }, 0i); }', "(assert (not (is-@Result-err Main@main)))");
    });
});

describe ("SMT -- Lambda calls (with template)", () => {
    it("should smt exec simple lambda template", function () {
        runishMainCodeUnsat("function foo<T>(x: T, f: fn(T) -> T): T { return f(x); } public function main(): Int { return foo<Int>(3i, fn(x) => x); }", "(assert (not (= 3 Main@main)))");
    });
});
