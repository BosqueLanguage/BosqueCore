"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Methods Pre/Post", () => {
    it("should emit simple entity methods", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int ensures $return > 0i; { return this.f; }} public function main(): Int { return Foo{3i}.foo(); }', 'Int Mainᕒmain() { MainᕒFoo ᐸtmp_0ᐳ = MainᕒFoo{3_i}; Int ᐸtmp_1ᐳ = MainᕒFooᑀfoo(ᐸtmp_0ᐳ); ᐸRuntimeᐳ::bsq_ensures((bool)(MainᕒFooᑀfooᐤensures_0(ᐸtmp_1ᐳ, ᐸtmp_0ᐳ)), "test.bsq", 2, nullptr, "Failed Ensures"); return ᐸtmp_1ᐳ; }'); 
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int requires this.f > 0i; { return this.f; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', 'Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; ᐸRuntimeᐳ::bsq_requires((bool)(MainᕒFooᑀfooᐤrequires_0(x)), "test.bsq", 2, nullptr, "Failed Requires"); return MainᕒFooᑀfoo(x); }'); 
    });
});
