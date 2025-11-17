"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- NamespaceFunction", () => {
    it("should smt exec simple code", function () {
        runishMainCodeUnsat("function bar(x: Int): Int { return x + 1i; } public function main(): Int { return bar(2i); }", "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat("function bar(x: Int): Int { return x + 1i; } public function main(): Int { return bar(2i) + bar(1i); }", "(assert (not (= 5 Main@main)))");

        runishMainCodeUnsat("function bar(x: Int): Int { assert x != 0i; return x + 1i; } public function main(): Int { return bar(2i); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int): Int { assert x != 0i; return x + 1i; } public function main(): Int { return bar(0i); }", "(assert (not (is-@Result-err Main@main)))");

        runishMainCodeUnsat("function bar(x: Int): Int { return x + 1i; } public function main(): Int { let v: Option<Int> = some(2i); return bar(v@some); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int): Int { return x + 1i; } public function main(): Int { let v: Option<Int> = none; return bar(v@some); }", "(assert (not (is-@Result-err Main@main)))");
    });

    it("should smt exec simple named", function () {
        runishMainCodeUnsat("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(x=1i, y=true); }", "(assert (not (= 1 Main@main)))");
        runishMainCodeUnsat("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "(assert (not (= 1 Main@main)))");
    });

    it("should smt exec simple mixed", function () {
        runishMainCodeUnsat("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(1i, y=true); }", "(assert (not (= 1 Main@main)))");
        runishMainCodeUnsat("function foo(x: Int, y: Bool): Int { return x; } public function main(): Int { return foo(y=true, x=1i); }", "(assert (not (= 1 Main@main)))");
    });

    it("should smt exec simple default", function () {
        runishMainCodeUnsat("function foo(x: Int, y: Int = 1i): Int { return x + y; } public function main(): Int { return foo(1i, 2i); }", "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat("function foo(x: Int, y: Int = 1i): Int { return x + y; } public function main(): Int { return foo(1i); }", "(assert (not (= 2 Main@main)))");
    });

    /*
    it("should smt exec dep default", function () {
        runMainCode("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i, 2i); }", "3i");
        runMainCode("function foo(x: Int, y: Int = $x): Int { return x + y; } public function main(): Int { return foo(1i); }", "2i");
    });
    */

    it("should smt exec templates", function () {
        runishMainCodeUnsat("function identity<T>(x: T): T { return x; } public function main(v: Bool): Int { return if(identity<Bool>(v)) then identity<Int>(0i) else 1i; }", "(assert (not (= 0 (Main@main true))))");
    });

    it("should smt exec simple lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(2i, fn(a) => a + 1i); }", "(assert (not (= 3 Main@main)))");

        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { assert x != 0i; return f(x); } public function main(): Int { return bar(2i, fn(a) => a + 1i); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { assert x != 0i; return f(x); } public function main(): Int { return bar(0i, fn(a) => a + 1i); }", "(assert (not (is-@Result-err Main@main)))");
    });

    it("should smt exec error lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(2i, fn(a) => { assert a != 0i; return a + 1i; }); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(0i, fn(a) => { assert a != 0i; return a + 1i; }); }", "(assert (not (is-@Result-err Main@main)))");
    });

    it("should smt exec both lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(2i, fn(a) => a + 1i) + bar(1i, fn(a) => { assert a != 0i; return a + 1i; }); }", "(assert (not (= (@Result-ok 5) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(0i, fn(a) => { assert a != 0i; return a + 1i; }) + bar(2i, fn(a) => a + 1i); }", "(assert (not (is-@Result-err Main@main)))");
    });

    it("should smt exec nested lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return baz(x, fn(a) => f(a) + 1i); } function baz(x: Int, g: fn(Int) -> Int): Int { return g(x); } public function main(): Int { return bar(2i, fn(a) => { return a + 1i; }); }", "(assert (not (= 4 Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(0i, fn(a) => { assert a != 0i; return a + 1i; }); }", "(assert (not (is-@Result-err Main@main)))");
    });
});

describe ("SMT Exec -- NamespaceFunction (with template)", () => {
    it("should smt exec simple positional", function () {
        runishMainCodeUnsat("function foo<T>(x: T): T { return x; } public function main(): Int { return foo<Int>(1i); }", "(assert (not (= 1 Main@main)))");
    });

    it("should smt exec two instantiations", function () {
        runishMainCodeUnsat("function foo<T>(x: T): T { return x; } public function main(): Int { if(foo<Nat>(1n) > 0n) { return foo<Int>(1i); } return 0i; }", "(assert (not (= 1 Main@main)))");
    });
});
