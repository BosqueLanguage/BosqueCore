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
