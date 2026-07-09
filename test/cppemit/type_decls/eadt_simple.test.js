"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- eADT decl", () => {
    it("should emit simple eADT", function () {
        checkTestEmitMainFunction('datatype Foo of F1 { field f: Int; } F2 { }; public function main(): Int { return F1{3i}.f; }', 'Int Mainᕒmain() { MainᕒF1 tmp_0 = MainᕒF1{3_i}; return tmp_0.f; }'); 
        checkTestEmitMainFunction('datatype Foo of F1 { field f: Int; invariant $f >= 0i; } F2 { field g: Bool; }; public function main(): Bool { return F2{false}.g; }', 'Bool Mainᕒmain() { MainᕒF2 tmp_0 = MainᕒF2{FALSE}; return tmp_0.g; }'); 

        checkTestEmitMainFunction('datatype Foo<T> of F1 { field f: T; } F2 { }; public function main(): Int { return F1<Int>{3i}.f; }', 'Int Mainᕒmain() { MainᕒF1ᐸIntᐳ tmp_0 = MainᕒF1ᐸIntᐳ{3_i}; return tmp_0.f; }'); 
    });

    it("should check eADT const", function () {
        checkTestEmitMainFunction('datatype Foo of F1 { field f: Int; } F2 { } & { const c: Int = 3i; } public function main(): Int { return F1::c; }', 'Int Mainᕒmain() { return 3_i; }'); 
        checkTestEmitMainFunction('datatype Foo of F1 { field f: Int; } F2 { } & { const c: Int = 3i; } public function main(): Int { return Foo::c; }', 'Int Mainᕒmain() { return 3_i; }'); 
    });

    it("should check eADT function", function () {
        checkTestEmitMainFunction('datatype Foo of F1 { field f: Int; } F2 { } & { function foo(): Int { return 3i; } } public function main(): Int { return F1::foo(); }', 'Int Mainᕒmain() { return MainᕒFooᕒfoo(); }'); 
        checkTestEmitMainFunction('datatype Foo of F1 { field f: Int; } F2 { } & { function foo(): Int { return 3i; } } public function main(): Int { return Foo::foo(); }', 'Int Mainᕒmain() { return MainᕒFooᕒfoo(); }'); 
    });
});

describe ("Checker -- eADT decl inherits", () => {
    it("should check simple inherits eADT", function () {
        checkTestEmitMainFunction('datatype Foo using { field f: Int; } of F1 { } F2 { }; public function main(): Int { return F1{3i}.f; }', 'Int Mainᕒmain() { MainᕒF1 tmp_0 = MainᕒF1{3_i}; return tmp_0.f; }'); 
        checkTestEmitMainFunction('datatype Foo using { field f: Int; invariant $f >= 0i; } of F1 { } F2 { field g: Bool; }; public function main(): Bool { return F2{3i, false}.g; }', 'Bool Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(3_i)), "test.bsq", 2, nullptr, "Failed Invariant"); MainᕒF2 tmp_0 = MainᕒF2{3_i, FALSE}; return tmp_0.g; }'); 

        checkTestEmitMainFunction('datatype Foo<T> using { field f: T; } of F1 { } F2 { }; public function main(): Int { return F1<Int>{3i}.f; }', 'Int Mainᕒmain() { MainᕒF1ᐸIntᐳ tmp_0 = MainᕒF1ᐸIntᐳ{3_i}; return tmp_0.f; }'); 

        checkTestEmitMainFunction('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of F1 { invariant $g ==> $f >= 0i; } F2 { }; public function main(): Int { return F1{3i, true}.f; }', 'Int Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒF1ᐤinvariant_0(3_i, TRUE)), "test.bsq", 2, nullptr, "Failed Invariant"); MainᕒF1 tmp_0 = MainᕒF1{3_i, TRUE}; return tmp_0.f; }'); 
    });
});
