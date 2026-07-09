"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";


describe ("CPPEmit-- Type Alias Constructor", () => {
    it("should emit simple type alias", function () {
        checkTestEmitMainFunction('type Foo = Int; public function main(): Foo { return Foo{1i}; }', 'MainᕒFoo Mainᕒmain() { return MainᕒFoo{1_i}; }');
    });
});

describe ("CPPEmit-- Type Alias w/ Invariant Constructor", () => {
    it("should emit type alias with invariant", function () {
        checkTestEmitMainFunction('type Foo = Int & { invariant $value > 3i; } public function main(): Foo { return Foo{4i}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(4_i)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{4_i}; }');
    });
});
