"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Lambda calls (no template, no capture)", () => {
    it("should emit simple lambda", function () {
        checkTestEmitMainFunction("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { return foo(fn(x: Int): Int => { return x + 1i; }); }", 'Int Mainᕒmain() { return Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}); }');
        checkTestEmitMainFunction("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { return foo(fn(x) => { return x + 1i; }); }", 'Int Mainᕒmain() { return Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}); }');

        checkTestEmitMainFunction("function foo(f: fn(Int) -> Int, z: Int): Int { return f(z); } public function main(y: Int): Int { return foo(fn(x) => x + 5i, y) + foo(fn(x) => x * 2i, y); }", 'Int Mainᕒmain(Int y) { Int tmp_0 = Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}, y); Int tmp_1 = Mainᕒfooᑅfn_1ᑀ(fn_1_ldata_{}, y); ᐸRuntimeᐳ::XInt::checkOverflowAddition(tmp_0, tmp_1, "test.bsq", 2); return tmp_0 + tmp_1; }');
    });
});
