"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it, run } from "node:test";

describe ("Exec -- Lambda ref calls", () => {
    it("should exec simple ref full", function () {
        runMainCode('entity Foo { field v: Int; } function foo(f: fn(ref Foo) -> Int): Int { var x = Foo{ 1i }; return f(ref x); } public function main(): Int { return foo(fn(ref x: Foo): Int => x.v); }', "1i");
        runMainCode('entity Foo { field v: Int; } function foo(f: fn(ref Foo) -> Int): Int { var x = Foo{ 1i }; let b = f(ref x); return b + x.v; } public function main(): Int { let a = foo(fn(ref x: Foo): Int => { ref x[v = 2i]; return 1i; }); return a; }', "3i");
    });
});

