"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- basic strict equals", () => {
    it("should emit strict equals operations", function () {
        checkTestEmitMainFunction("public function main(): Bool { return 0n === 1n; }", "Bool Mainᕒmain() { return 0_n == 1_n; }");
        checkTestEmitMainFunction("public function main(): Bool { return 0n !== 1n; }", "bbb");
        checkTestEmitMainFunction("public function main(): Bool { return 'ok' !== 'yes'; }", "ccc");

        checkTestEmitMainFunction("public function main(): Bool { let x = 3i; let y = 4i; return x !== y; }", "ddd");
        checkTestEmitMainFunction("public function main(): Bool { let x = 3i; let y = 4i; return x === y; }", "eee");
    });
});

describe ("CPPEmit -- Some strict equals", () => {
    it("should emit strict equals some operations", function () {
        checkTestEmitMainFunction("public function main(): Bool { let x: Some<Int> = some(3i); return x === 3i; }", "Bool Mainᕒmain() { SomeᐸIntᐳ x = SomeᐸIntᐳ{3_i}; return 3_i == x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Some<Int> = some(4i); return 3i === x; }", "ggg");
        checkTestEmitMainFunction("public function main(): Bool { let x: Some<Int> = some(3i); return x !== 3i; }", "hhh");
        checkTestEmitMainFunction("public function main(): Bool { let x: Some<Int> = some(4i); return 3i !== x; }", "iii");
    });
});

describe ("CPPEmit -- Option strict equals", () => {
    it("should emit strict equals option operations", function () {
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return x === none; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{3_i}); return x.isNone(); }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return x !== none; }", "kkk");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return none === x; }", "lll");

        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return x === none; }", "mmm");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return x !== none; }", "nnn");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return none === x; }", "ooo");

        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return x === 3i; }", "ppp");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return 3i === x; }", "qqq");

        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return x === 3i; }", "rrr");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(4i); return 3i === x; }", "sss");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return x !== 3i; }", "ttt");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(4i); return 3i !== x; }", "uuu");
    });
});

describe ("CPPEmit -- type alias strict equals", () => {
    it("should emit type alias strict equals operations", function () {
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return 1i<Foo> === 1i<Foo>; }", "Bool Mainᕒmain() { return MainᕒFoo{1_i} == MainᕒFoo{1_i}; }");
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return 1i<Foo> !== 1i<Foo>; }", "xxx");

        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x === none; }", "yyy");
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 0i<Foo>; }", "zzz");
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 3i<Foo>; }", "111");
    });
});


describe ("CPPEmit -- enum strict equals", () => {
    it("should emit enum strict equals operations", function () {
        checkTestEmitMainFunction("enum Foo { f, g } public function main(): Bool { return Foo#f === Foo#f; }", "Bool Mainᕒmain() { return MainᕒFoo::f == MainᕒFoo::f; }");
        checkTestEmitMainFunction("enum Foo { f, g } public function main(): Bool { return Foo#f !== Foo#f; }", "333");
    });
});
