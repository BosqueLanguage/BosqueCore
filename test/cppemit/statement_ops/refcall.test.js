"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- ref call statements", () => {
    it("should emit ref call statements", function () {
        checkTestEmitMainFunction('entity Foo { field x: Int; } function foo(ref z: Foo) { ; } public function main(): Int { ref z = Foo{3i}; foo(ref z); return z.x; }', 'Int Mainᕒmain() { MainᕒFoo z = MainᕒFoo{3_i}; Mainᕒfooᙾref(z); return z.x; }');
        checkTestEmitMainFunction('entity Foo { field x: Int; ref method foo() { ; } } public function main(): Int { ref z = Foo{3i}; ref z.foo(); return z.x; }', 'Int Mainᕒmain() { MainᕒFoo z = MainᕒFoo{3_i}; MainᕒFooᑀfooᙾref(z); return z.x; }');
    });
});
