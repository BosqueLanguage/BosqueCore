"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- entity simple", () => {
    it("should emit simple entity", function () {
        checkTestEmitMainFunction("entity Foo { field f: Int; } public function main(): Foo { return Foo{3i}; }", "MainᕒFoo Mainᕒmain() { return MainᕒFoo{3_i}; }"); 
        checkTestEmitMainFunction("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Foo { return Foo{3i}; }", 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(3_i)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{3_i}; }'); 

        checkTestEmitMainFunction("entity Foo<T> { field f: T; } public function main(): Foo<Int> { return Foo<Int>{3i}; }", "MainᕒFooᐸIntᐳ Mainᕒmain() { return MainᕒFooᐸIntᐳ{3_i}; }");
    });
});

describe ("CPPEmit -- entity simple with default fields", () => {
    it("should emit simple entity", function () {
        checkTestEmitMainFunction("entity Foo { field f: Int = 3i; } public function main(): Foo { return Foo{}; }", "MainᕒFoo Mainᕒmain() { return MainᕒFoo{3_i}; }"); 

        checkTestEmitMainFunction("entity Foo { field f: Int; field g: Int = 2i; } public function main(): Foo { return Foo{3i, 5i}; }", "MainᕒFoo Mainᕒmain() { return MainᕒFoo{3_i, 5_i}; }"); 
        checkTestEmitMainFunction("entity Foo { field f: Int; field g: Int = 2i; } public function main(): Foo { return Foo{3i}; }", "MainᕒFoo Mainᕒmain() { return MainᕒFoo{3_i, 2_i}; }"); 
    });
});

describe ("CPPEmit -- entity decl with consts", () => {
    it("should emit entity with consts", function () {
        checkTestEmitMainFunction('entity Foo { const c: Int = 3i; } public function main(): Int { return Foo::c; }', "Int Mainᕒmain() { return 3_i; }"); 
        checkTestEmitMainFunction('entity Foo<T> { const c: Int = 3i; } public function main(): Int { return Foo<Nat>::c; }', "Int Mainᕒmain() { return 3_i; }"); 
    });
});

describe ("CPPEmit -- entity decl of number with invariants", () => {
    it("should emit entity with invariants", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Foo { return Foo{3i}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(3_i)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{3_i}; }'); 
        checkTestEmitMainFunction('entity Foo { field f: Int; invariant $f > 0i; invariant $f <= 100i; } public function main(): Int { let x = Foo{50i}; return 5i; }', 'Int Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(50_i)), "test.bsq", 2, nullptr, "Failed Invariant"); ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_1(50_i)), "test.bsq", 2, nullptr, "Failed Invariant"); MainᕒFoo x = MainᕒFoo{50_i}; return 5_i; }');    

        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; invariant $g ==> $f > 3i; } public function main(): Foo { return Foo{1i, false}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(1_i, FALSE)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{1_i, FALSE}; }');
    });
});

describe ("CPPEmit -- entity decl with functions", () => {
    it("should emit entity with functions", function () {
        checkTestEmitMainFunction('entity Foo { function foo(): Int { return 3i; } } public function main(): Int { return Foo::foo(); }', "Int Mainᕒmain() { return MainᕒFooᕒfoo(); }");

        checkTestEmitMainFunction('entity Foo<T> { function foo(x: T): T { return x; } } public function main(): Int { return Foo<Int>::foo(3i); }', "Int Mainᕒmain() { return MainᕒFooᐸIntᐳᕒfoo(3_i); }");
        checkTestEmitMainFunction('entity Foo { function foo<T>(x: T): T { return x; } } public function main(): Int { return Foo::foo<Int>(3i); }', "Int Mainᕒmain() { return MainᕒFooᕒfooᐸIntᐳ(3_i); }");
    });
});


