"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- If Statement", () => {
    it("should emit simple ifs (simplify)", function () {
        checkTestEmitMainFunction("public function main(): Int { if(true) { return 3i; } return 1i; }", "Int Mainᕒmain() { return 3_i; }");
        checkTestEmitMainFunction("public function main(): Int { if(false) { return 3i; } return 1i; }", "Int Mainᕒmain() { return 1_i; }");

        checkTestEmitMainFunction("public function main(): Int { if(true || false) { return 3i; } return 1i; }", "Int Mainᕒmain() { return 3_i; }");
        checkTestEmitMainFunction("public function main(): Int { if(true && true) { return 3i; } return 1i; }", "Int Mainᕒmain() { return 3_i; }");
    });

    it("should emit simple ifs general", function () {
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b) { return 3i; } return 1i; }", "Int Mainᕒmain(Bool b) { if(b) { return 3_i; } return 1_i; }");
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b && true) { return 3i; } return 1i; }", "Int Mainᕒmain(Bool b) { if(b) { return 3_i; } return 1_i; }");
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b || true) { return 3i; } return 1i; }", "Int Mainᕒmain(Bool b) { return 3_i; }");
    });

    it("should emit type alias ifs", function () {
        checkTestEmitMainFunction("type Foo = Bool; public function main(): Int { if(true<Foo>) { return 3i; } return 1i; }", "Int Mainᕒmain() { if(MainᕒFoo{TRUE}.value) { return 3_i; } return 1_i; }");
        checkTestEmitMainFunction("type Foo = Bool; public function main(b: Foo): Int { if(b) { return 3i; } return 1i; }", "Int Mainᕒmain(MainᕒFoo b) { if(b.value) { return 3_i; } return 1_i; }");
    });

    it("should emit ifs w/ single itest specials", function () {
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if (x)!none { return 1i; } return 3i; }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { return 1_i; } return 3_i; }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if (x)some { return 1i; } return 3i; }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { return 1_i; } return 3_i; }');
        
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if (x)@!none { return $x; } return 3i; }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { Int ᑯx = x.unwrap(); return ᑯx; } return 3_i; }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if (x)@some { return $x; } return 3i; }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { Int ᑯx = x.unwrap(); return ᑯx; } return 3_i; }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { if ($z = x)@some { return $z; } return 3i; }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { if(!x.isNone()) { Int ᑯz = x.unwrap(); return ᑯz; } return 3_i; }');

        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); if (x)@some { return $x; } return 1i; }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; if(!x.isNone()) { Int ᑯx = x.unwrap(); return ᑯx; } return 1_i; }');
        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@some { return $y; } return 1i; }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; if(!x.isNone()) { Int ᑯy = x.unwrap(); return ᑯy; } return 1_i; }');
    
        checkTestEmitMainFunction("public function main(x: Option<Option<Int>>): Int { if (x.@some)@some { return $_; } return 3i; }", 'Int Mainᕒmain(OptionᐸOptionᐸIntᐳᐳ x) { ᐸRuntimeᐳ::bsq_typeassert((bool)(!x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); OptionᐸIntᐳ tmp_0 = x.unwrap(); if(!tmp_0.isNone()) { Int ᑯ_ = tmp_0.unwrap(); return ᑯ_; } return 3_i; }');
    });

    it("should emit ifs w/ single itest types", function () {
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if (x)<Foo> { return 1i; } return 3i; }", 'Int Mainᕒmain(MainᕒBar x) { if(x.uval.isTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo)) { return 1_i; } return 3_i; }');

        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if (x)@<Foo> { return $x.f; } return 3i; }", 'Int Mainᕒmain(MainᕒBar x) { if(x.uval.isTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo)) { MainᕒFoo ᑯx = x.uval.data.u_MainᕒFoo; return ᑯx.f; } return 3_i; }');
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if (x)@!<Foo> { return 1i; } return 3i; }", 'Int Mainᕒmain(MainᕒBar x) { if(x.uval.isNotTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo)) { MainᕒBar ᑯx = x; return 1_i; } return 3_i; }');
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if ($y = x)@<Foo> { return $y.f; } return 3i; }", 'Int Mainᕒmain(MainᕒBar x) { if(x.uval.isTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo)) { MainᕒFoo ᑯy = x.uval.data.u_MainᕒFoo; return ᑯy.f; } return 3_i; }');

        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); if (x)@<Some<Int>> { return $x.value; } return 1i; }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; if(!x.isNone()) { SomeᐸIntᐳ ᑯx = x.asSome(); return ᑯx.value; } return 1_i; }');
        checkTestEmitMainFunction("public function main(): Int { let x: Option<Int> = some(3i); if ($y = x)@<Some<Int>> { return $y.value; } return 1i; }", 'Int Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; if(!x.isNone()) { SomeᐸIntᐳ ᑯy = x.asSome(); return ᑯy.value; } return 1_i; }');
    });

    it.todo("should emit ifs w/ multi itest", function () {
    });

    it.todo("should emit ifs w/ passing params", function () {
    });
});
