"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- entity methods", () => {
    it("should exec simple entity methods", function () {
        runMainCode('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { return Foo{3i}.foo(); }', "3i"); 
        runMainCode('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', "3i"); 
    });

    it("should exec simple entity methods with args", function () {
        runMainCode('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} public function main(): Int { return Foo{3i}.foo(1i); }', "4i"); 
        runMainCode('entity Foo { field f: Int; method foo(x: Int = 1i): Int { return this.f + x; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', "4i"); 
    });

    it("should exec simple entity methods with template", function () {
        runMainCode('entity Foo { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} public function main(): Bool { let x = Foo{3i}; return x.foo<Nat>(); }', "false"); 
        runMainCode('entity Foo { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} public function main(): Bool { let x = Foo{3i}; return x.foo<Int>(); }', "true"); 
    });

    it("should exec simple entity methods with type template", function () {
        runMainCode('entity Foo<T> { field f: T; method foo(x: T): T { return if (true) then x else this.f; }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo(2i); }', "2i"); 
    });

    it("should exec simple entity methods with both template", function () {
        runMainCode('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} public function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Nat>(); }', "false"); 
        runMainCode('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} public function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Int>(); }', "true"); 
    });

    it("should exec simple entity methods with both template and more", function () {
        runMainCode('entity Foo<T> { field f: T; method foo<U>(u: U): U { return if (this.f)@<U> then $_ else u; }} public function main(): Nat { let x = Foo<Int>{3i}; return x.foo<Nat>(3n); }', "3n"); 
        runMainCode('entity Foo<T> { field f: T; method foo<U>(t: T): T { return if (t)<U> then t else this.f; }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo<Int>(3i); }', "3i"); 
    });
});

describe ("Exec -- eADT methods", () => {
    it("should exec simple eADT methods", function () {
        runMainCode('datatype Foo of | Foo1 { field f: Int; method foo(): Int { return this.f; }} ; public function main(): Int { return Foo1{3i}.foo(); }', "3i"); 
        runMainCode('datatype Foo of | Foo1 { field f: Int; method foo(x: Int): Int { return this.f + x; }} ; public function main(): Int { return Foo1{3i}.foo(1i); }', "4i"); 
    });

    it("should exec simple eADT methods with template", function () {
        runMainCode('datatype Foo of | Foo1 { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} ; public function main(): Bool { let x = Foo1{3i}; return x.foo<Nat>(); }', "false"); 
        runMainCode('datatype Foo of | Foo1 { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} ; public function main(): Bool { let x = Foo1{3i}; return x.foo<Int>(); }', "true"); 
    });

    it("should exec simple eADT methods with type template", function () {
        runMainCode('datatype Foo<T> of |Foo1 { field f: T; method foo(x: T): T { return if (true) then x else this.f; }} ; public function main(): Int { let x = Foo1<Int>{3i}; return x.foo(2i); }', "2i"); 
    });

    it("should exec simple ROOT eADT methods", function () {
        runMainCode('datatype Foo of | F1 { } | F2 { } & { method foo(): Int { return if(this)<F1> then 1i else 0i; } } public function main(): Int { return F1{}.foo(); }', "1i"); 

        runMainCode('datatype Foo of | F1 { f: Int } | F2 { g: Int } & { method foo(): Int { if(this)@<F1> { return $this.f; } else { return $this.g; } } } public function main(): Int { return F1{3i}.foo(); }', "3i"); 

        runMainCode('datatype Foo of | F1 { f: Int } | F2 { g: Int } & { method foo(): Int { if(this)@<F1> { return $this.f; } else { return $this.g + 1i; } } } public function main(): Int { let x: Foo = F1{3i}; return x.foo(); }', "3i"); 
        runMainCode('datatype Foo of | F1 { f: Int } | F2 { g: Int } & { method foo(): Int { if(this)@<F1> { return $this.f; } else { return $this.g + 1i; } } } public function main(): Int { let x: Foo = F2{3i}; return x.foo(); }', "4i"); 
    });

    it("should exec template ROOT eADT methods", function () {
        runMainCode('datatype Foo<T> of | F1 { } | F2 { } & { method foo(): Int { return if(this)<F1<T>> then 1i else 0i; } } public function main(): Int { return F1<Bool>{}.foo(); }', "1i"); 

        runMainCode('datatype Foo<T> of | F1 { f: T } | F2 { g: T } & { method foo(): T { if(this)@<F1<T>> { return $this.f; } else { return $this.g; } } } public function main(): Int { return F1<Int>{3i}.foo(); }', "3i"); 
        runMainCode('datatype Foo<T> of | F1 { f: T } | F2 { g: T } & { method foo(): T { if(this)@<F1<T>> { return $this.f; } else { return $this.g; } } } public function main(): Int { let x: Foo<Int> = F1<Int>{3i}; return x.foo(); }', "3i"); 
    });
});

describe ("Exec -- type alias methods", () => {
    it("should exec simple type alias methods", function () {
        runMainCode('type Foo = Int & { method foo(): Int { return this.value; }} public function main(): Int { return 3i<Foo>.foo(); }', "3i"); 
        runMainCode('type Foo = Int & { method foo(x: Int): Int { return this.value + x; }} public function main(): Int { return 3i<Foo>.foo(1i); }', "4i"); 
    });

    it("should exec simple type alias methods with template", function () {
        runMainCode('type Foo = Int & { method foo<T>(): Bool { return this.value?<T>; }} public function main(): Bool { let x = 3i<Foo>; return x.foo<Nat>(); }', "false"); 
        runMainCode('type Foo = Int & { method foo<T>(): Bool { return this.value?<T>; }} public function main(): Bool { let x = 3i<Foo>; return x.foo<Int>(); }', "true"); 
    });
});
