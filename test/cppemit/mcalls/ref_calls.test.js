"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- entity ref methods", () => {
    it("should emit simple entity ref methods", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; ref method foo(): Int { return this.f; }} public function main(): Int { var x = Foo{3i}; return ref x.foo(); }', "Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; Int tmp_0 = MainᕒFooᑀfooᙾref(x); return tmp_0; }"); 
    });
});

describe ("CPPEmit -- eADT ref methods", () => {
    it("should emit simple eADT ref methods", function () {
        checkTestEmitMainFunction('datatype Foo of Foo1 { field f: Int; ref method foo(x: Int): Int { return this.f + x; }} ; public function main(): Int { var x = Foo1{3i}; return ref x.foo(1i); }', "Int Mainᕒmain() { MainᕒFoo1 x = MainᕒFoo1{3_i}; Int tmp_0 = MainᕒFoo1ᑀfooᙾref(x, 1_i); return tmp_0; }"); 
    });
});
