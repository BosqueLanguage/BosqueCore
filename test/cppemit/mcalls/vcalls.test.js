"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

const conceptcode_abstract = 'concept Bar { abstract method foo(): Int; }';
const conceptcode_virtual = 'concept Bar { virtual method foo(): Int { return 0i; } }';

const conceptcode_optabstract = 'concept Bar { abstract method foo(): Option<Int>; }';
const conceptcode_optvirtual = 'concept Bar { virtual method foo(): Option<Int> { return some(0i); } }';

describe ("CPPEmit -- entity abstract/virtual methods", () => {
    it("should emit simple abstract/virtual (virtual calls) methods", function () {
        checkTestEmitMainFunction(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} public function main(): Int { let v = Foo{3i}; return v.foo(); }`, 'Int Mainᕒmain() { MainᕒFoo v = MainᕒFoo{3_i}; return MainᕒFooᑀfoo(v); }'); 
        checkTestEmitMainFunction(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } public function main(): Int { let x = Foo{3i}; return x.foo(); }`, 'Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; return MainᕒBarᑀfoo(MainᕒBar{x}); }'); 

        checkTestEmitMainFunction(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} public function main(): Int { let v: Bar = Foo{3i}; return v.foo(); }`, 'Int Mainᕒmain() { MainᕒBar v = MainᕒBar{MainᕒFoo{3_i}}; return MainᕒBarᑀfooᕒ_vcall_(v); }'); 
        checkTestEmitMainFunction(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } public function main(): Int { let x: Bar = Foo{3i}; return x.foo(); }`, 'Int Mainᕒmain() { MainᕒBar x = MainᕒBar{MainᕒFoo{3_i}}; return MainᕒBarᑀfooᕒ_vcall_(x); }'); 
    });

    it("should emit simple abstract/virtual (vary result) methods", function () {
        checkTestEmitMainFunction(`${conceptcode_optabstract} entity Foo provides Bar { field f: Int; override method foo(): Some<Int> { return some(this.f); }} public function main(): Int { let v: Bar = Foo{3i}; return v.foo().@some; }`, 'Int Mainᕒmain() { MainᕒBar v = MainᕒBar{MainᕒFoo{3_i}}; OptionᐸIntᐳ ᐸtmp_0ᐳ = MainᕒBarᑀfooᕒ_vcall_(v); ᐸRuntimeᐳ::bsq_typeassert((bool)(!ᐸtmp_0ᐳ.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return ᐸtmp_0ᐳ.unwrap(); }'); 
        checkTestEmitMainFunction(`${conceptcode_optvirtual} entity Foo provides Bar { field f: Int; } public function main(): Int { let x: Bar = Foo{3i}; return x.foo().@some; }`, 'Int Mainᕒmain() { MainᕒBar x = MainᕒBar{MainᕒFoo{3_i}}; OptionᐸIntᐳ ᐸtmp_0ᐳ = MainᕒBarᑀfooᕒ_vcall_(x); ᐸRuntimeᐳ::bsq_typeassert((bool)(!ᐸtmp_0ᐳ.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return ᐸtmp_0ᐳ.unwrap(); }'); 
    });

    it("should emit simple abstract/virtual (2 opts) methods", function () {
        checkTestEmitMainFunction(`${conceptcode_abstract} entity Foo provides Bar { field f: Int; override method foo(): Int { return this.f; }} entity Fizz provides Bar { override method foo(): Int { return 10i; }} public function main(): Int { let v: Bar = Foo{3i}; return v.foo(); }`, 'Int Mainᕒmain() { MainᕒBar v = MainᕒBar{MainᕒFoo{3_i}}; return MainᕒBarᑀfooᕒ_vcall_(v); }'); 
        checkTestEmitMainFunction(`${conceptcode_virtual} entity Foo provides Bar { field f: Int; } entity Fizz provides Bar { override method foo(): Int { return 10i; }} public function main(): Int { let x: Bar = Foo{3i}; return x.foo(); }`, 'Int Mainᕒmain() { MainᕒBar x = MainᕒBar{MainᕒFoo{3_i}}; return MainᕒBarᑀfooᕒ_vcall_(x); }'); 
    });

    it("should emit simple abstract/virtual (requires/ensures) methods", function () {
        checkTestEmitMainFunction(`concept Bar { abstract method foo(): Int ensures $return >= 0i; ; } entity Foo provides Bar { override method foo(): Int { return 0i; } } public function main(): Int { let v: Foo = Foo{}; let u: Bar = Foo{}; return v.foo() + u.foo(); }`, 'Int Mainᕒmain() { MainᕒFoo v = MainᕒFoo{}; MainᕒBar u = MainᕒBar{MainᕒFoo{}}; MainᕒBar ᐸtmp_0ᐳ = MainᕒBar{v}; Int ᐸtmp_1ᐳ = MainᕒFooᑀfoo(v); ᐸRuntimeᐳ::bsq_ensures((bool)(MainᕒBarᑀfooᐤensures_0(ᐸtmp_1ᐳ, ᐸtmp_0ᐳ)), "test.bsq", 2, nullptr, "Failed Ensures"); Int ᐸtmp_2ᐳ = MainᕒBarᑀfooᕒ_vcall_(u); ᐸRuntimeᐳ::bsq_ensures((bool)(MainᕒBarᑀfooᐤensures_0(ᐸtmp_2ᐳ, u)), "test.bsq", 2, nullptr, "Failed Ensures"); ᐸRuntimeᐳ::XInt::checkOverflowAddition(ᐸtmp_1ᐳ, ᐸtmp_2ᐳ, "test.bsq", 2); return ᐸtmp_1ᐳ + ᐸtmp_2ᐳ; }'); 
        checkTestEmitMainFunction(`concept Bar { virtual method foo(): Int ensures $return >= 0i; { return 5i; } } entity Foo provides Bar { } public function main(): Int { let v: Foo = Foo{}; let u: Bar = Foo{}; return v.foo() + u.foo(); }`, 'Int Mainᕒmain() { MainᕒFoo v = MainᕒFoo{}; MainᕒBar u = MainᕒBar{MainᕒFoo{}}; MainᕒBar ᐸtmp_0ᐳ = MainᕒBar{v}; Int ᐸtmp_1ᐳ = MainᕒBarᑀfoo(ᐸtmp_0ᐳ); ᐸRuntimeᐳ::bsq_ensures((bool)(MainᕒBarᑀfooᐤensures_0(ᐸtmp_1ᐳ, ᐸtmp_0ᐳ)), "test.bsq", 2, nullptr, "Failed Ensures"); Int ᐸtmp_2ᐳ = MainᕒBarᑀfooᕒ_vcall_(u); ᐸRuntimeᐳ::bsq_ensures((bool)(MainᕒBarᑀfooᐤensures_0(ᐸtmp_2ᐳ, u)), "test.bsq", 2, nullptr, "Failed Ensures"); ᐸRuntimeᐳ::XInt::checkOverflowAddition(ᐸtmp_1ᐳ, ᐸtmp_2ᐳ, "test.bsq", 2); return ᐸtmp_1ᐳ + ᐸtmp_2ᐳ; }'); 
    });
});
