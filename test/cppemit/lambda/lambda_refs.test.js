"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Lambda ref calls", () => {
    it("should emit simple ref", function () {
        checkTestEmitMainFunction('function foo(f: fn(inout Int) -> Int): Int { var x = 1i; return f(inout x); } public function main(): Int { return foo(fn(inout x: Int): Int => x); }', 'Int Mainᕒmain() { return Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}); }');
        checkTestEmitMainFunction('entity Foo { field v: Int; } function foo(f: fn(ref Foo) -> Int): Int { var x = Foo{ 1i }; return f(ref x); } public function main(): Int { return foo(fn(ref x: Foo): Int => x.v); }', 'Int Mainᕒmain() { return Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}); }');
    });
});
