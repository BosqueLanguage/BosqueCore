"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- entity methods", () => {
    it("should emit simple entity methods", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { return Foo{3i}.foo(); }', "Int Mainᕒmain() { MainᕒFoo tmp_0 = MainᕒFoo{3_i}; return MainᕒFooᑀfoo(tmp_0); }"); 
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', "Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; return MainᕒFooᑀfoo(x); }"); 
    });

    it("should emit simple entity methods with args", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} public function main(): Int { return Foo{3i}.foo(1i); }', "Int Mainᕒmain() { MainᕒFoo tmp_0 = MainᕒFoo{3_i}; return MainᕒFooᑀfoo(tmp_0, 1_i); }"); 
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(x: Int = 1i): Int { return this.f + x; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', "Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; return MainᕒFooᑀfoo(x, 1_i); }"); 
    });

    it("should emit simple entity methods with template", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo<T>(): Bool { return this.f.?<T>; }} public function main(): Bool { let x = Foo{3i}; return x.foo<Nat>(); }', "Bool Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; return MainᕒFooᑀfooᐸNatᐳ(x); }"); 
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo<T>(): Bool { return this.f.?<T>; }} public function main(): Bool { let x = Foo{3i}; return x.foo<Int>(); }', "Bool Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; return MainᕒFooᑀfooᐸIntᐳ(x); }"); 
    });

    it("should emit simple entity methods with type template", function () {
        checkTestEmitMainFunction('entity Foo<T> { field f: T; method foo(x: T): T { if(true) { return x; } else { return this.f; } }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo(2i); }', "Int Mainᕒmain() { MainᕒFooᐸIntᐳ x = MainᕒFooᐸIntᐳ{3_i}; return MainᕒFooᐸIntᐳᑀfoo(x, 2_i); }"); 
    });

    it("should emit simple entity methods with both template", function () {
        checkTestEmitMainFunction('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f.?<U>; }} public function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Nat>(); }', "Bool Mainᕒmain() { MainᕒFooᐸIntᐳ x = MainᕒFooᐸIntᐳ{3_i}; return MainᕒFooᐸIntᐳᑀfooᐸNatᐳ(x); }"); 
        checkTestEmitMainFunction('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f.?<U>; }} public function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Int>(); }', "Bool Mainᕒmain() { MainᕒFooᐸIntᐳ x = MainᕒFooᐸIntᐳ{3_i}; return MainᕒFooᐸIntᐳᑀfooᐸIntᐳ(x); }"); 
    });

    it("should emit simple entity methods with both template and more", function () {
        checkTestEmitMainFunction('entity Foo<T> { field f: T; method foo<U>(u: U): U { if (this.f)@<U> { return $_; } else { return u; } }} public function main(): Nat { let x = Foo<Int>{3i}; return x.foo<Nat>(3n); }', "jjj"); 
        checkTestEmitMainFunction('entity Foo<T> { field f: T; method foo<U>(t: T): T { if (t)<U> { return t; } else { return this.f; } }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo<Int>(3i); }', "kkk"); 
    });

    it("should emit simple entity methods multiple options", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int { return this.f; } method foo(out x: Int): Int { x = 3i; return x; } } public function main(): Int { return Foo{3i}.foo(); }', "Int Mainᕒmain() { MainᕒFoo tmp_0 = MainᕒFoo{3_i}; return MainᕒFooᑀfoo(tmp_0); }"); 
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int { return this.f; } method foo(out x: Int): Int { x = 3i; return x; } } public function main(): Int { let x = Foo{3i}; var y: Int; return x.foo(out y); }', "Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; Int y; Int tmp_0 = MainᕒFooᑀfooᙾref(x, y); return tmp_0; }");
        checkTestEmitMainFunction('entity Foo { field f: Int; method foo(): Int { return this.f; } method foo(f: fn() -> Int): Int { return f(); } } public function main(): Int { let x = Foo{3i}; return x.foo(fn() => 3i); }', "Int Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; return MainᕒFooᑀfooᑅfn_0ᑀ(x, fn_0_ldata_{}); }");
    });
});

describe ("CPPEmit -- eADT methods", () => {
    it("should emit simple eADT methods", function () {
        checkTestEmitMainFunction('datatype Foo of Foo1 { field f: Int; method foo(): Int { return this.f; }} ; public function main(): Int { return Foo1{3i}.foo(); }', "Int Mainᕒmain() { MainᕒFoo1 tmp_0 = MainᕒFoo1{3_i}; return MainᕒFoo1ᑀfoo(tmp_0); }"); 
        checkTestEmitMainFunction('datatype Foo of Foo1 { field f: Int; method foo(x: Int): Int { return this.f + x; }} ; public function main(): Int { return Foo1{3i}.foo(1i); }', "Int Mainᕒmain() { MainᕒFoo1 tmp_0 = MainᕒFoo1{3_i}; return MainᕒFoo1ᑀfoo(tmp_0, 1_i); }"); 
    });

    it("should emit simple eADT methods with template", function () {
        checkTestEmitMainFunction('datatype Foo of Foo1 { field f: Int; method foo<T>(): Bool { return this.f.?<T>; }} ; public function main(): Bool { let x = Foo1{3i}; return x.foo<Nat>(); }', "Bool Mainᕒmain() { MainᕒFoo1 x = MainᕒFoo1{3_i}; return MainᕒFoo1ᑀfooᐸNatᐳ(x); }"); 
        checkTestEmitMainFunction('datatype Foo of Foo1 { field f: Int; method foo<T>(): Bool { return this.f.?<T>; }} ; public function main(): Bool { let x = Foo1{3i}; return x.foo<Int>(); }', "Bool Mainᕒmain() { MainᕒFoo1 x = MainᕒFoo1{3_i}; return MainᕒFoo1ᑀfooᐸIntᐳ(x); }"); 
    });

    it("should emit simple eADT methods with type template", function () {
        checkTestEmitMainFunction('datatype Foo<T> of Foo1 { field f: T; method foo(x: T): T { if(true) { return x; } else { return this.f; } }} ; public function main(): Int { let x = Foo1<Int>{3i}; return x.foo(2i); }', "Int Mainᕒmain() { MainᕒFoo1ᐸIntᐳ x = MainᕒFoo1ᐸIntᐳ{3_i}; return MainᕒFoo1ᐸIntᐳᑀfoo(x, 2_i); }"); 
    });

    it("should emit simple ROOT eADT methods", function () {
        checkTestEmitMainFunction('datatype Foo of F1 { } F2 { } & { method foo(): Int { if(this)<F1> { return 1i; } else { return 0i; } } } public function main(): Int { return F1{}.foo(); }', "Int Mainᕒmain() { MainᕒF1 tmp_0 = MainᕒF1{}; return MainᕒFooᑀfoo(MainᕒFoo(tmp_0)); }"); 

        checkTestEmitMainFunction('datatype Foo of F1 { f: Int } F2 { g: Int } & { method foo(): Int { if(this)@<F1> { return $this.f; } else { return $this.g; } } } public function main(): Int { return F1{3i}.foo(); }', "Int Mainᕒmain() { MainᕒF1 tmp_0 = MainᕒF1{3_i}; return MainᕒFooᑀfoo(MainᕒFoo(tmp_0)); }"); 
    });

    it("should emit template ROOT eADT methods", function () {
        checkTestEmitMainFunction('datatype Foo<T> of F1 { } F2 { } & { method foo(): Int { if(this)<F1<T>> { return  1i; } return 0i; } } public function main(): Int { return F1<Bool>{}.foo(); }', "Int Mainᕒmain() { MainᕒF1ᐸBoolᐳ tmp_0 = MainᕒF1ᐸBoolᐳ{}; return MainᕒFooᐸBoolᐳᑀfoo(MainᕒFooᐸBoolᐳ(tmp_0)); }"); 

        checkTestEmitMainFunction('datatype Foo<T> of F1 { f: T } F2 { g: T } & { method foo(): T { if(this)@<F1<T>> { return $this.f; } else { return $this.g; } } } public function main(): Int { return F1<Int>{3i}.foo(); }', "Int Mainᕒmain() { MainᕒF1ᐸIntᐳ tmp_0 = MainᕒF1ᐸIntᐳ{3_i}; return MainᕒFooᐸIntᐳᑀfoo(MainᕒFooᐸIntᐳ(tmp_0)); }"); 
    });
});

describe ("Checker -- type alias methods", () => {
    it("should emit simple type alias methods", function () {
        checkTestEmitMainFunction('type Foo = Int & { method foo(): Int { return this.value; }} public function main(): Int { return 3i<Foo>.foo(); }', "Int Mainᕒmain() { return MainᕒFooᑀfoo(MainᕒFoo{3_i}); }"); 
        checkTestEmitMainFunction('type Foo = Int & { method foo(x: Int): Int { return this.value + x; }} public function main(): Int { return 3i<Foo>.foo(1i); }', "Int Mainᕒmain() { return MainᕒFooᑀfoo(MainᕒFoo{3_i}, 1_i); }"); 
    });

    it("should emit simple type alias methods with template", function () {
        checkTestEmitMainFunction('type Foo = Int & { method foo<T>(): Bool { return this.value.?<T>; }} public function main(): Bool { let x = 3i<Foo>; return x.foo<Nat>(); }', "Bool Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; return MainᕒFooᑀfooᐸNatᐳ(x); }"); 
        checkTestEmitMainFunction('type Foo = Int & { method foo<T>(): Bool { return this.value.?<T>; }} public function main(): Bool { let x = 3i<Foo>; return x.foo<Int>(); }', "Bool Mainᕒmain() { MainᕒFoo x = MainᕒFoo{3_i}; return MainᕒFooᑀfooᐸIntᐳ(x); }"); 
    });
});
