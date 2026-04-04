"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Lambda calls (no template, no capture)", () => {
    it("should emit simple lambda", function () {
        checkTestEmitMainFunction("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { return foo(fn(x: Int): Int => { return x + 1i; }); }", 'Int Mainᕒmain() { return Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}); }');
        checkTestEmitMainFunction("function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { return foo(fn(x) => { return x + 1i; }); }", 'Int Mainᕒmain() { return Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}); }');

        checkTestEmitMainFunction("function gg(x: Int): Int { return x + 1i; } function foo(f: fn(Int) -> Int): Int { return f(1i); } public function main(): Int { return foo(fn(x: Int): Int => { return gg(x); }); }", 'Int Mainᕒmain() { return Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}); }');
        checkTestEmitMainFunction("function foo(f: fn(Int) -> Int, z: Int): Int { return f(z); } public function main(y: Int): Int { return foo(fn(x) => x + 5i, y) + foo(fn(x) => x * 2i, y); }", 'Int Mainᕒmain(Int y) { Int tmp_0 = Mainᕒfooᑅfn_0ᑀ(fn_0_ldata_{}, y); Int tmp_1 = Mainᕒfooᑅfn_1ᑀ(fn_1_ldata_{}, y); ᐸRuntimeᐳ::XInt::checkOverflowAddition(tmp_0, tmp_1, "test.bsq", 2); return tmp_0 + tmp_1; }');
    });
});

describe ("CPPEmit -- Lambda calls (with template)", () => {
    it("should emit simple lambda template", function () {
        checkTestEmitMainFunction("function foo<T>(x: T, f: fn(T) -> T): T { return f(x); } public function main(): Int { return foo<Int>(3i, fn(x) => x); }", 'Int Mainᕒmain() { return MainᕒfooᐸIntᐳᑅfn_0ᑀ(3_i, fn_0_ldata_{}); }');
        checkTestEmitMainFunction("function foo<T>(x: T, f: fn(T) -> T): T { return f(x); } public function main(): Nat { if(foo<Int>(3i, fn(x) => x) > 0i) { return foo<Nat>(3n, fn(x) => x); } return 0n; }", 'Nat Mainᕒmain() { Int tmp_0 = MainᕒfooᐸIntᐳᑅfn_0ᑀ(3_i, fn_0_ldata_{}); if(tmp_0 > 0_i) { return MainᕒfooᐸNatᐳᑅfn_1ᑀ(3_n, fn_1_ldata_{}); } return 0_n; }');

        checkTestEmitMainFunction("function xis<T>(x: T, f: fn(T) -> T): T { return f(x); } function foo<T>(v: T): T { return xis<T>(v, fn(x) => x@<T>); } public function main(): Int { return foo<Int>(3i); }", 'www');
    });
});

