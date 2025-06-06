"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- NamespaceFunction", () => {
    it("should exec simple code", function () {
        runishMainCodeUnsat("function bar(x: Int): Int { return x + 1i; } public function main(): Int { return bar(2i); }", "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat("function bar(x: Int): Int { return x + 1i; } public function main(): Int { return bar(2i) + bar(1i); }", "(assert (not (= 5 Main@main)))");

        runishMainCodeUnsat("function bar(x: Int): Int { assert x != 0i; return x + 1i; } public function main(): Int { return bar(2i); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int): Int { assert x != 0i; return x + 1i; } public function main(): Int { return bar(0i); }", "(assert (not (= @Result-err-other Main@main)))");
    });

    it("should exec simple lambda", function () {
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { return f(x); } public function main(): Int { return bar(2i, fn(a) => a + 1i); }", "(assert (not (= 3 Main@main)))");

        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { assert x != 0i; return f(x); } public function main(): Int { return bar(2i, fn(a) => a + 1i); }", "(assert (not (= (@Result-ok 3) Main@main)))");
        runishMainCodeUnsat("function bar(x: Int, f: fn(Int) -> Int): Int { assert x != 0i; return f(x); } public function main(): Int { return bar(0i, fn(a) => a + 1i); }", "(assert (not (= @Result-err-other Main@main)))");
    });
});
