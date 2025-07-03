"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- entity methods", () => {
    it("should exec simple entity methods", function () {
        runMainCode('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { return Foo{3i}.foo(); }', "3_i"); 
        runMainCode('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', "3_i"); 
    });

    it("should exec simple entity methods with args", function () {
        runMainCode('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} public function main(): Int { return Foo{3i}.foo(1i); }', "4_i"); 
        //runMainCode('entity Foo { field f: Int; method foo(x: Int = 1i): Int { return this.f + x; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', "4_i"); 
    });

    it("should exec simple entity methods with named args", function () {
        runMainCode('entity Foo { field f: Int; method foo(x: Int, y: Int): Int { return this.f + x + y; }} public function main(): Int { return Foo{3i}.foo(x=1i,y=2i); }', "6_i"); 
    });

    it("should exec simple entity methods with template args", function () {
        runMainCode('entity Foo { method foo<T>(x: T, y: T): T { return y; }} public function main(): Int { return Foo{}.foo<Int>(1i, 2i); }', "2_i");
    });
    it("should exec simple entity methods with multiple template args", function () {
        runMainCode('entity Foo { method foo<T, K>(x: T, y: K): T { return x; }} public function main(): Int { return Foo{}.foo<Int, Nat>(2i, 1n); }', "2_i");
    });
    it("should exec simple entity methods with type template", function () {
        runMainCode('entity Foo<T> { field f: T; method foo(x: T): T { return if (true) then x else this.f; }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo(2i); }', "2_i"); 
    });

    it("should exec simple entity methods with both template", function () {
        runMainCode('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} public function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Nat>(); }', "false"); 
        runMainCode('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} public function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Int>(); }', "true"); 
    });
});

describe ("CPP Emit Evaluate -- eADT methods", () => {
    it("should exec simple eADT methods", function () {
        runMainCode('datatype Foo of Foo1 { field f: Int; method foo(): Int { return this.f; }} ; public function main(): Int { return Foo1{3i}.foo(); }', "3_i"); 
        runMainCode('datatype Foo of Foo1 { field f: Int; method foo(x: Int): Int { return this.f + x; }} ; public function main(): Int { return Foo1{3i}.foo(1i); }', "4_i"); 
    });

    it("should exec simple eADT methods with type template", function () {
        runMainCode('datatype Foo<T> of Foo1 { field f: T; method foo(x: T): T { return if (true) then x else this.f; }} ; public function main(): Int { let x = Foo1<Int>{3i}; return x.foo(2i); }', "2_i"); 
    });
   
    it("should exec simple eADT methods with template", function () {
        runMainCode('datatype Foo of Foo1 { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} ; public function main(): Bool { let x = Foo1{3i}; return x.foo<Nat>(); }', "false"); 
        runMainCode('datatype Foo of Foo1 { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} ; public function main(): Bool { let x = Foo1{3i}; return x.foo<Int>(); }', "true"); 
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
