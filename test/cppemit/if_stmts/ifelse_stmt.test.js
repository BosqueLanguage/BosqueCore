"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- ElseIf Statement", () => {
    it("should emit simple else ifs (simplify)", function () {
        checkTestEmitMainFunction("public function main(): Int { if(true) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { return 3_i; }");
        checkTestEmitMainFunction("public function main(): Int { if(false) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { return 1_i; }");

        checkTestEmitMainFunction("public function main(): Int { if(true || false) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { return 3_i; }");
        checkTestEmitMainFunction("public function main(): Int { if(true && true) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { return 3_i; }");
    });

    it("should emit simple else ifs general", function () {
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b) { return 3i; } else { return 1i; } }", "Int Mainᕒmain(Bool b) { if(b) { return 3_i; } else { return 1_i; } }");
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b) { return 3i; } else { assert 4i < 5i; } return 1i; }", 'Int Mainᕒmain(Bool b) { if(b) { return 3_i; } else { ᐸRuntimeᐳ::bsq_assert((bool)(4_i < 5_i), "test.bsq", 2, nullptr, "Assertion Failed"); } return 1_i; }');

        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b && true) { return 3i; } else { return 1i; } }", "Int Mainᕒmain(Bool b) { if(b) { return 3_i; } else { return 1_i; } }");
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b || true) { return 3i; } else { return 1i; } }", "Int Mainᕒmain(Bool b) { return 3_i; }");
    });

    it("should emit type alias else ifs", function () {
        checkTestEmitMainFunction("type Foo = Bool; public function main(): Int { if(true<Foo> || false<Foo>) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { if((MainᕒFoo{((MainᕒFoo{TRUE}.value) | (MainᕒFoo{FALSE}.value))}).value) { return 3_i; } else { return 1_i; } }");
        checkTestEmitMainFunction("type Foo = Bool; public function main(b: Foo): Int { if(b || !!b) { return 3i; } else { return 1i; } }", "Int Mainᕒmain(MainᕒFoo b) { if((MainᕒFoo{((b.value) | ((MainᕒFoo{(!((MainᕒFoo{(!(b.value))}).value))}).value))}).value) { return 3_i; } else { return 1_i; } }");
    });

    it("should emit if-else w/ single itest specials", function () {
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if (x)!none { return 1i; } else { return 3i; } }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { return 1_i; } else { return 3_i; } }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if (x)some { return 1i; } else { return 3i; } }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { return 1_i; } else { return 3_i; } }');

        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if (x)@none { return 3i; } else { return $x; } }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(x.isNone()) { None ᑯx = none; return 3_i; } else { Int ᑯx = x.unwrap(); return ᑯx; } }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if (x)@some { return $x; } else { return 3i; } }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { Int ᑯx = x.unwrap(); return ᑯx; } else { None ᑯx = none; return 3_i; } }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if ($z = x)@some { return $z; } else { return 3i; } }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { Int ᑯz = x.unwrap(); return ᑯz; } else { None ᑯz = none; return 3_i; } }');

        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); if (x)@some { return $x; } else { return 1i; } }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; if(!x.isNone()) { Int ᑯx = x.unwrap(); return ᑯx; } else { None ᑯx = none; return 1_i; } }');
        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@!some { return 1i; } else { return $y; } }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; if(x.isNone()) { None ᑯy = none; return 1_i; } else { Int ᑯy = x.unwrap(); return ᑯy; } }');
    
        checkTestEmitMainFunction("public function main(x: Option<Option<Int>>): Int { if (x.@some)@some { return $_; } else { return 3i; } }", 'Int Mainᕒmain(OptionᐸOptionᐸIntᐳᐳ x) { ᐸRuntimeᐳ::bsq_typeassert((bool)(!x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); OptionᐸIntᐳ tmp_0 = x.unwrap(); if(!tmp_0.isNone()) { Int ᑯ_ = tmp_0.unwrap(); return ᑯ_; } else { None ᑯ_ = none; return 3_i; } }');
    });

    it("should emit if-else w/ single itest types", function () {
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if (x)<Foo> { return 1i; } else { return 3i; } }", 'Int Mainᕒmain(MainᕒBar x) { if(x.uval.isTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo)) { return 1_i; } else { return 3_i; } }');

        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if (x)@<Foo> { return $x.f; } else { return 3i; } }", 'Int Mainᕒmain(MainᕒBar x) { if(x.uval.isTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo)) { MainᕒFoo ᑯx = x.uval.data.u_MainᕒFoo; return ᑯx.f; } else { MainᕒBar ᑯx = x; return 3_i; } }');
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if (x)@!<Foo> { return 1i; } else { return 3i; } }", 'Int Mainᕒmain(MainᕒBar x) { if(x.uval.isNotTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo)) { MainᕒBar ᑯx = x; return 1_i; } else { MainᕒFoo ᑯx = x.uval.data.u_MainᕒFoo; return 3_i; } }');
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if ($y = x)@<Foo> { return $y.f; } else { return 3i; } }", 'Int Mainᕒmain(MainᕒBar x) { if(x.uval.isTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo)) { MainᕒFoo ᑯy = x.uval.data.u_MainᕒFoo; return ᑯy.f; } else { MainᕒBar ᑯy = x; return 3_i; } }');

        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); if (x)@<Some<Int>> { return $x.value; } else { return 1i; } }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; if(!x.isNone()) { SomeᐸIntᐳ ᑯx = x.asSome(); return ᑯx.value; } else { None ᑯx = none; return 1_i; } }');
        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@<Some<Int>> { return $y.value; } else { return 1i; } }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; if(!x.isNone()) { SomeᐸIntᐳ ᑯy = x.asSome(); return ᑯy.value; } else { None ᑯy = none; return 1_i; } }');
    });

    it.todo("should emit if-else w/ multi itest", function () {
    });

    it.todo("should emit if-else w/ passing params", function () {
    });

    it("should emit simple if-elif-else", function () {
        checkTestEmitMainFunction("public function main(x: Int): Int { if(x == 0i) { return 0i; } elif(x > 0i) { return 1i; } else { return -1i; } }", 'Int Mainᕒmain(Int x) { if(x == 0_i) { return 0_i; } else { if(x > 0_i) { return 1_i; } else { return -1_i; } } }');
    });
});
