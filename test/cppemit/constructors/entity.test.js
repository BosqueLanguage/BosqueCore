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
