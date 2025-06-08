"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- NamespaceFunction", () => {
    it("should smt exec simple code", function () {
        runishMainCodeUnsat("function bar(x: Int): Int { return x + 1i; } public function main(): Int { return bar(2i); }", "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat("function bar(x: Int): Int { return x + 1i; } public function main(): Int { return bar(2i) + bar(1i); }", "(assert (not (= 5 Main@main)))");

        runishMainCodeUnsat("function bar(x: Int): Int { assert x != 0i; return x + 1i; } public function main(): Int { return bar(2i); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int): Int { assert x != 0i; return x + 1i; } public function main(): Int { return bar(0i); }", "(assert (not (= @Result-err-other Main@main)))");
    });

    it("should smt exec simple lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(2i, fn(a) => a + 1i); }", "(assert (not (= 3 Main@main)))");

        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { assert x != 0i; return f(x); } public function main(): Int { return bar(2i, fn(a) => a + 1i); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { assert x != 0i; return f(x); } public function main(): Int { return bar(0i, fn(a) => a + 1i); }", "(assert (not (= @Result-err-other Main@main)))");
    });

    it("should smt exec error lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(2i, fn(a) => { assert a != 0i; return a + 1i; }); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(0i, fn(a) => { assert a != 0i; return a + 1i; }); }", "(assert (not (= @Result-err-other Main@main)))");
    });

    it("should smt exec both lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(2i, fn(a) => a + 1i) + bar(1i, fn(a) => { assert a != 0i; return a + 1i; }); }", "(assert (not (= (@Result-ok 5) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(0i, fn(a) => { assert a != 0i; return a + 1i; }) + bar(2i, fn(a) => a + 1i); }", "(assert (not (= @Result-err-other Main@main)))");
    });

    it("should smt exec nested lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return baz(x, fn(a) => f(a) + 1i); } function baz(x: Int, g: fn(Int) -> Int): Int { return g(x); } public function main(): Int { return bar(2i, fn(a) => { return a + 1i; }); }", "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(0i, fn(a) => { assert a != 0i; return a + 1i; }); }", "(assert (not (= @Result-err-other Main@main)))");
    });
});
