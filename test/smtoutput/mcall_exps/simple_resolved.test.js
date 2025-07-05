"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT Exec -- entity methods", () => {
    it("should smt exec simple entity methods", function () {
        runishMainCodeUnsat('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { return Foo{3i}.foo(); }', "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', "(assert (not (= 3 Main@main)))"); 
    });

    it("should smt exec simple entity methods with args", function () {
        runishMainCodeUnsat('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} public function main(): Int { return Foo{3i}.foo(1i); }', "(assert (not (= 4 Main@main)))"); 
    });

    it("should smt exec simple entity methods with template", function () {
        runishMainCodeUnsat('entity Foo { field f: Int; method foo<T>(): Bool { return false; }} public function main(): Bool { let x = Foo{3i}; return x.foo<Nat>(); }', "(assert (not (= false Main@main)))"); 
        runishMainCodeUnsat('entity Foo { field f: Int; method foo<T>(): Bool { return true; }} public function main(): Bool { let x = Foo{3i}; return x.foo<Int>(); }', "(assert (not (= true Main@main)))"); 
    });

    it("should smt exec simple entity methods with type template", function () {
        runishMainCodeUnsat('entity Foo<T> { field f: T; method foo(x: T): T { return this.f; }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo(2i); }', "(assert (not (= 3 Main@main)))"); 
    });

    it("should smt exec simple entity methods with/wo errors", function () {
        runishMainCodeUnsat('entity Foo { field x: Int; method m(y: Int): Int { assert y != 0i; return this.x + y; } } public function main(): Int { let foo = Foo{ 3i }; return foo.m(2i); }', "(assert (not (= (@Result-ok 5) Main@main)))");

        runishMainCodeUnsat('entity Foo { field x: Int; method m(y: Int): Int { return this.x + y; } } public function main(): Int { let foo: Option<Foo> = none; return foo@some.m(2i); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('entity Foo { field x: Int; method m(y: Int): Int { return this.x + y; } } public function main(): Int { let foo: Option<Foo> = some(Foo{ 3i }); return foo@some.m(2i); }', "(assert (not (= (@Result-ok 5) Main@main)))");
    });

    it("should smt exec simple entity methods with both template and more", function () {
        runishMainCodeUnsat('entity Foo<T> { field f: T; method foo<U>(u: U): U { return if (this.f)@<U> then $_ else u; }} public function main(): Nat { let x = Foo<Int>{3i}; return x.foo<Nat>(3n); }', "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat('entity Foo<T> { field f: T; method foo<U>(t: T): T { return if (t)<U> then t else this.f; }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo<Int>(3i); }', "(assert (not (= 3 Main@main)))");
    });
});

describe ("SMT Exec -- entity methods (Pre/Post)", () => {
    it("should smt exec simple entity methods", function () {
        runishMainCodeUnsat('entity Foo { field f: Int; method foo(): Int requires this.f != 0i; { return this.f; }} public function main(a: Int): Int { return Foo{a}.foo(); }', "(assert (not (= (@Result-ok 3) (Main@main 3))))"); 
        runishMainCodeUnsat('entity Foo { field f: Int; method foo(): Int requires this.f != 0i; { return this.f; }} public function main(a: Int): Int { return Foo{a}.foo(); }', "(assert (not (is-@Result-err (Main@main 0))))"); 
    });
});

/*
describe ("Exec -- eADT methods", () => {
    it("should exec simple eADT methods", function () {
        runMainCode('datatype Foo of Foo1 { field f: Int; method foo(): Int { return this.f; }} ; public function main(): Int { return Foo1{3i}.foo(); }', "3i"); 
        runMainCode('datatype Foo of Foo1 { field f: Int; method foo(x: Int): Int { return this.f + x; }} ; public function main(): Int { return Foo1{3i}.foo(1i); }', "4i"); 
    });

    it("should exec simple eADT methods with template", function () {
        runMainCode('datatype Foo of Foo1 { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} ; public function main(): Bool { let x = Foo1{3i}; return x.foo<Nat>(); }', "false"); 
        runMainCode('datatype Foo of Foo1 { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} ; public function main(): Bool { let x = Foo1{3i}; return x.foo<Int>(); }', "true"); 
    });

    it("should exec simple eADT methods with type template", function () {
        runMainCode('datatype Foo<T> of Foo1 { field f: T; method foo(x: T): T { return if (true) then x else this.f; }} ; public function main(): Int { let x = Foo1<Int>{3i}; return x.foo(2i); }', "2i"); 
    });

    it("should exec simple ROOT eADT methods", function () {
        runMainCode('datatype Foo of F1 { } | F2 { } & { method foo(): Int { return if(this)<F1> then 1i else 0i; } } public function main(): Int { return F1{}.foo(); }', "1i"); 

        runMainCode('datatype Foo of F1 { f: Int } | F2 { g: Int } & { method foo(): Int { if(this)@<F1> { return $this.f; } else { return $this.g; } } } public function main(): Int { return F1{3i}.foo(); }', "3i"); 

        runMainCode('datatype Foo of F1 { f: Int } | F2 { g: Int } & { method foo(): Int { if(this)@<F1> { return $this.f; } else { return $this.g + 1i; } } } public function main(): Int { let x: Foo = F1{3i}; return x.foo(); }', "3i"); 
        runMainCode('datatype Foo of F1 { f: Int } | F2 { g: Int } & { method foo(): Int { if(this)@<F1> { return $this.f; } else { return $this.g + 1i; } } } public function main(): Int { let x: Foo = F2{3i}; return x.foo(); }', "4i"); 
    });

    it("should exec template ROOT eADT methods", function () {
        runMainCode('datatype Foo<T> of F1 { } | F2 { } & { method foo(): Int { return if(this)<F1<T>> then 1i else 0i; } } public function main(): Int { return F1<Bool>{}.foo(); }', "1i"); 

        runMainCode('datatype Foo<T> of F1 { f: T } | F2 { g: T } & { method foo(): T { if(this)@<F1<T>> { return $this.f; } else { return $this.g; } } } public function main(): Int { return F1<Int>{3i}.foo(); }', "3i"); 
        runMainCode('datatype Foo<T> of F1 { f: T } | F2 { g: T } & { method foo(): T { if(this)@<F1<T>> { return $this.f; } else { return $this.g; } } } public function main(): Int { let x: Foo<Int> = F1<Int>{3i}; return x.foo(); }', "3i"); 
    });
});
*/
describe ("SMT -- type alias methods", () => {
    it("should smt exec simple type alias methods", function () {
        runishMainCodeUnsat('type Foo = Int & { method foo(): Int { return this.value; }} public function main(): Int { return 3i<Foo>.foo(); }', "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat('type Foo = Int & { method foo(x: Int): Int { return this.value + x; }} public function main(): Int { return 3i<Foo>.foo(1i); }', "(assert (not (= 4 Main@main)))"); 
    });

    it("should smt exec simple type alias methods with template", function () {
        runishMainCodeUnsat('type Foo = Int & { method foo<T>(): Bool { return this.value?<T>; }} public function main(): Bool { let x = 3i<Foo>; return x.foo<Nat>(); }', "(assert Main@main)"); 
        runishMainCodeUnsat('type Foo = Int & { method foo<T>(): Bool { return this.value?<T>; }} public function main(): Bool { let x = 3i<Foo>; return x.foo<Int>(); }', "(assert (not Main@main))"); 
    });
});

