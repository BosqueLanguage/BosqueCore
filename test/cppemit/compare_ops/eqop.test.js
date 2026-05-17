"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- basic strict equals", () => {
    it("should emit strict equals operations", function () {
        checkTestEmitMainFunction("public function main(): Bool { return 0n === 1n; }", "Bool Mainᕒmain() { return 0_n == 1_n; }");
        checkTestEmitMainFunction("public function main(): Bool { return 0n !== 1n; }", "Bool Mainᕒmain() { return 0_n != 1_n; }");
        checkTestEmitMainFunction("public function main(): Bool { return 'ok' !== 'yes'; }", 'Bool Mainᕒmain() { return "ok"_cs != "yes"_cs; }');

        checkTestEmitMainFunction("public function main(): Bool { let x = 3i; let y = 4i; return x !== y; }", "Bool Mainᕒmain() { Int x = 3_i; Int y = 4_i; return x != y; }");
        checkTestEmitMainFunction("public function main(): Bool { let x = 3i; let y = 4i; return x === y; }", "Bool Mainᕒmain() { Int x = 3_i; Int y = 4_i; return x == y; }");
    });
});

describe ("CPPEmit -- Some strict equals", () => {
    it("should emit strict equals some operations", function () {
        checkTestEmitMainFunction("public function main(): Bool { let x: Some<Int> = some(3i); return x === 3i; }", "Bool Mainᕒmain() { SomeᐸIntᐳ x = SomeᐸIntᐳ{3_i}; return 3_i == x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Some<Int> = some(4i); return 3i === x; }", "Bool Mainᕒmain() { SomeᐸIntᐳ x = SomeᐸIntᐳ{4_i}; return 3_i == x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Some<Int> = some(3i); return x !== 3i; }", "Bool Mainᕒmain() { SomeᐸIntᐳ x = SomeᐸIntᐳ{3_i}; return 3_i != x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Some<Int> = some(4i); return 3i !== x; }", "Bool Mainᕒmain() { SomeᐸIntᐳ x = SomeᐸIntᐳ{4_i}; return 3_i != x; }");
    });
});

describe ("CPPEmit -- Option strict equals", () => {
    it("should emit strict equals option operations", function () {
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return x === none; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{3_i}); return x.isNone(); }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return x !== none; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{3_i}); return !x.isNone(); }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return none === x; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{3_i}); return x.isNone(); }");

        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return x === none; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::optnone; return x.isNone(); }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return x !== none; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::optnone; return !x.isNone(); }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return none === x; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::optnone; return x.isNone(); }");

        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return x === 3i; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::optnone; return 3_i == x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = none; return 3i === x; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::optnone; return 3_i == x; }");

        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return x === 3i; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{3_i}); return 3_i == x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(4i); return 3i === x; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{4_i}); return 3_i == x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(3i); return x !== 3i; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{3_i}); return 3_i != x; }");
        checkTestEmitMainFunction("public function main(): Bool { let x: Option<Int> = some(4i); return 3i !== x; }", "Bool Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{4_i}); return 3_i != x; }");
    });
});

describe ("CPPEmit -- type alias strict equals", () => {
    it("should emit type alias strict equals operations", function () {
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return 1i<Foo> === 1i<Foo>; }", "Bool Mainᕒmain() { return MainᕒFoo{1_i} == MainᕒFoo{1_i}; }");
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return 1i<Foo> !== 1i<Foo>; }", "Bool Mainᕒmain() { return MainᕒFoo{1_i} != MainᕒFoo{1_i}; }");

        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x === none; }", "Bool Mainᕒmain() { OptionᐸMainᕒFooᐳ x = OptionᐸMainᕒFooᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸMainᕒFooᐳ, SomeᐸMainᕒFooᐳ{MainᕒFoo{3_i}}); return x.isNone(); }");
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 0i<Foo>; }", "Bool Mainᕒmain() { OptionᐸMainᕒFooᐳ x = OptionᐸMainᕒFooᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸMainᕒFooᐳ, SomeᐸMainᕒFooᐳ{MainᕒFoo{3_i}}); return MainᕒFoo{0_i} != x; }");
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { let x: Option<Foo> = some(3i<Foo>); return x !== 3i<Foo>; }", "Bool Mainᕒmain() { OptionᐸMainᕒFooᐳ x = OptionᐸMainᕒFooᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸMainᕒFooᐳ, SomeᐸMainᕒFooᐳ{MainᕒFoo{3_i}}); return MainᕒFoo{3_i} != x; }");
    });
});


describe ("CPPEmit -- enum strict equals", () => {
    it("should emit enum strict equals operations", function () {
        checkTestEmitMainFunction("enum Foo { f, g } public function main(): Bool { return Foo#f === Foo#f; }", "Bool Mainᕒmain() { return MainᕒFoo::f == MainᕒFoo::f; }");
        checkTestEmitMainFunction("enum Foo { f, g } public function main(): Bool { return Foo#f !== Foo#f; }", "Bool Mainᕒmain() { return MainᕒFoo::f != MainᕒFoo::f; }");
    });
});
