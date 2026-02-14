"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- type decl of bool", () => {
    it("should emit bool type decl", function () {
        checkTestEmitMainFunction("type Flag = Bool; public function main(): Flag { let e = true<Flag>; return e; }", 'MainᕒFlag Mainᕒmain() { MainᕒFlag e = MainᕒFlag{TRUE}; return e; }'); 
    });
});

describe ("CPPEmit -- type decl of number", () => {
    it("should emit numeric type decls", function () {
        checkTestEmitMainFunction('type NVal = Int; public function main(): NVal { let e = -2i<NVal>; return e; }', 'MainᕒNVal Mainᕒmain() { MainᕒNVal e = MainᕒNVal{-2_i}; return e; }');
    });
});


describe ("CPPEmit -- type decl of number with invariants", () => {
    it("should emit positional", function () {
        checkTestEmitMainFunction('type Foo = Int & { invariant $value > 3i; } public function main(): Foo { let e = Foo{5i}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(5_i)), "test.bsq", 2, nullptr, "Failed Invariant"); MainᕒFoo e = MainᕒFoo{5_i}; return e; }');
    });
});
