"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Entity Constructor", () => {
    it("should emit positional", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; } public function main(): Foo { return Foo{1i}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i}; }");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; } public function main(): Foo { return Foo{1i, false}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i, FALSE}; }");
    });

    it("should emit nominal", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; } public function main(): Foo { return Foo{f = 1i}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i}; }");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; } public function main(): Foo { return Foo{1i, g = true}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i, TRUE}; }");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; } public function main(): Foo { return Foo{f=1i, g = true}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i, TRUE}; }");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; } public function main(): Foo { return Foo{ g = true, f=1i}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i, TRUE}; }");
    });

    it("should emit default", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int = 0i; } public function main(): Foo { return Foo{}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{0_i}; }");
        checkTestEmitMainFunction('entity Foo { field f: Int = 0i; } public function main(): Foo { return Foo{5i}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{5_i}; }");
    });

    it("should emit skip positions", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; field h: Int; } public function main(): Foo { return Foo{1i, _, 5i, g=true}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i, TRUE, 5_i}; }");
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool = true; field h: Int; } public function main(): Foo { return Foo{1i, _, h=5i}; }', "MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i, TRUE, 5_i}; }");
    });

    it("should emit nested and reference versions", function () {
        const bbar = 'entity Bar { field p: Int; field q: Int; field r: Int; }';
        const sbfoo = 'entity Foo { field a: Bar; field b: Bar; }';
        const lbfoo = 'entity Foo { field x: Int; field y: Int; field z: Int; field a: Bar; field b: Bar; }';
     
        checkTestEmitMainFunction(`${bbar} ${sbfoo} public function main(): Foo { return Foo{a = Bar{1i, 2i, 3i}, b = Bar{4i, 5i, 0i}}; }`, "MainᕒFoo Mainᕒmain() { MainᕒBar tmp_0 = MainᕒBar{1_i, 2_i, 3_i}; MainᕒBar tmp_1 = MainᕒBar{4_i, 5_i, 0_i}; return MainᕒFoo{tmp_0, tmp_1}; }");
        checkTestEmitMainFunction(`${bbar} ${lbfoo} public function main(): Foo { return Foo{1i, 2i, 3i, Bar{4i, 5i, 0i}, Bar{6i, 7i, 0i}}; }`, "MainᕒFoo* Mainᕒmain() { MainᕒBar tmp_0 = MainᕒBar{4_i, 5_i, 0_i}; MainᕒBar tmp_1 = MainᕒBar{6_i, 7_i, 0_i}; return ᐸRuntimeᐳ::MainᕒFoo_allocator.allocate(1_i, 2_i, 3_i, tmp_0, tmp_1); }"); 
    });
});

describe ("CPPEmit -- Entity w/ Invariant Constructor", () => {
    it("should emit positional", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; invariant $f > 3i; } public function main(): Foo { return Foo{4i}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(4_i)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{4_i}; }');
        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; invariant $g ==> $f > 3i; } public function main(): Foo { return Foo{1i, false}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(1_i, FALSE)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{1_i, FALSE}; }');

        checkTestEmitMainFunction('entity Foo { field f: Int; field g: Bool; invariant !$g; invariant $f != 0i; } public function main(): Foo { return Foo{1i, false}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(1_i, FALSE)), "test.bsq", 2, nullptr, "Failed Invariant"); ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_1(1_i, FALSE)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{1_i, FALSE}; }');
    });

    it("should emit default", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int = 0i; invariant $f != 3i; } public function main(): Foo { return Foo{5i}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(5_i)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{5_i}; }');
        checkTestEmitMainFunction('entity Foo { field f: Int = 0i; invariant $f != 3i; } public function main(): Foo { return Foo{}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(0_i)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{0_i}; }');
    });

    it.todo("should emit inherits single", function () {
    });

    it.todo("should emit inherits multiple", function () {
    });

    it.todo("should emit inherits with invariants too", function () {
    });
});
