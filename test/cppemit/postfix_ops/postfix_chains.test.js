"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Postfix Chains", () => {
    it("should emit simple postfix chains", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; } entity Bar { field g: Foo; } public function main(): Int { return Bar{Foo{3i}}.g.f; }', "Int Mainᕒmain() { MainᕒFoo tmp_0 = MainᕒFoo{3_i}; MainᕒBar* tmp_1 = ᐸRuntimeᐳ::MainᕒBar_allocator.allocate(tmp_0); return tmp_1->g.f; }");
        checkTestEmitMainFunction('type Bar = Int; entity Foo { field f: Bar; } public function main(): Int { let x = Foo{Bar{3i}}; return x.f.value; }', "Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{MainᕒBar{3_i}}; return x.f.value; }");

        checkTestEmitMainFunction('entity Foo { method f(x: Int): Int { return x; } } entity Bar { field g: Foo; } public function main(): Int { return Bar{Foo{}}.g.f(1i); }', "Int Mainᕒmain() { MainᕒFoo tmp_0 = MainᕒFoo{}; MainᕒBar* tmp_1 = ᐸRuntimeᐳ::MainᕒBar_allocator.allocate(tmp_0); return MainᕒFooᑀf(tmp_1->g, 1_i); }"); 
    });

    it("should emit postfix chains w/ ref", function () {
        checkTestEmitMainFunction('entity Foo { method f(inout x: Int): Int { return x; } } entity Bar { field g: Foo; } public function main(): Int { var y: Int = 0i; return Bar{Foo{}}.g.f(inout y); }', "Int Mainᕒmain() { Int y = 0_i; MainᕒFoo tmp_0 = MainᕒFoo{}; MainᕒBar* tmp_1 = ᐸRuntimeᐳ::MainᕒBar_allocator.allocate(tmp_0); Int tmp_2 = MainᕒFooᑀfᙾref(tmp_1->g, y); return tmp_2; }"); 
    });
});
