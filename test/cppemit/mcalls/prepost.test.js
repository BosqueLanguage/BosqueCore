"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Methods Pre/Post", () => {
    it("should emit simple entity methods", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int ensures $return > 0i; { return this.f; }} public function main(): Int { return Foo{3i}.foo(); }', 'Int Mainᕒmain() { MainᕒFoo tmp_0 = MainᕒFoo{3_i}; Int tmp_1 = MainᕒFooᑀfoo(tmp_0); ᐸRuntimeᐳ::bsq_ensures((bool)(MainᕒFooᑀfooᐤensures_0(tmp_1, tmp_0)), "test.bsq", 2, nullptr, "Failed Ensures"); return tmp_1; }'); 
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int requires this.f > 0i; { return this.f; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', 'Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; ᐸRuntimeᐳ::bsq_requires((bool)(MainᕒFooᑀfooᐤrequires_0(x)), "test.bsq", 2, nullptr, "Failed Requires"); return MainᕒFooᑀfoo(x); }'); 
    });
});
