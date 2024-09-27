"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- entity methods", () => {
    it("should exec simple entity methods", function () {
        runMainCode('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { return Foo{3i}.foo(); }', [3n, "Int"]); 
        runMainCode('entity Foo { field f: Int; method foo(): Int { return this.f; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', [3n, "Int"]); 
    });

    it("should exec simple entity methods with args", function () {
        runMainCode('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} public function main(): Int { return Foo{3i}.foo(1i); }', [4n, "Int"]); 
        runMainCode('entity Foo { field f: Int; method foo(x: Int = 1i): Int { return this.f + x; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', [4n, "Int"]); 
    });

    it("should exec simple entity methods with template", function () {
        runMainCode('entity Foo { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} public function main(): Bool { let x = Foo{3i}; return x.foo<Nat>(); }', [true, "Bool"]); 
        runMainCode('entity Foo { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} public function main(): Bool { let x = Foo{3i}; return x.foo<Int>(); }', [true, "Bool"]); 
    });

    it("should exec simple entity methods with type template", function () {
        runMainCode('entity Foo<T> { field f: T; method foo(x: T): T { return if (true) then x else this.f; }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo(2i); }', [2n, "Int"]); 
    });

    it("should exec simple entity methods with both template", function () {
        runMainCode('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} public function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Nat>(); }', [true, "Bool"]); 
        runMainCode('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} public function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Int>(); }', [true, "Bool"]); 
    });

    it("should exec simple entity methods with both template and more", function () {
        runMainCode('entity Foo<T> { field f: T; method foo<U>(u: U): U { return if (this.f)@<U> then $_ else u; }} public function main(): Nat { let x = Foo<Int>{3i}; return x.foo<Nat>(3n); }', [3n, "Nat"]); 
        runMainCode('entity Foo<T> { field f: T; method foo<U>(t: T): T { return if (t)<U> then t else this.f; }} public function main(): Int { let x = Foo<Int>{3i}; return x.foo<Int>(3i); }', [3n, "Int"]); 
    });
});
