"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- entity methods", () => {
    it("should check simple entity methods", function () {
        checkTestFunction('entity Foo { field f: Int; method foo(): Int { return this.f; }} function main(): Int { return Foo{3i}.foo(); }'); 
        checkTestFunction('entity Foo { field f: Int; method foo(): Int { return this.f; }} function main(): Int { let x = Foo{3i}; return x.foo(); }'); 
    });

    it("should check simple entity methods with args", function () {
        checkTestFunction('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} function main(): Int { return Foo{3i}.foo(1i); }'); 
        checkTestFunction('entity Foo { field f: Int; method foo(x: Int = 1i): Int { return this.f + x; }} function main(): Int { let x = Foo{3i}; return x.foo(); }'); 
    });

    it("should check simple entity methods with template", function () {
        checkTestFunction('entity Foo { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} function main(): Bool { let x = Foo{3i}; return x.foo<Nat>(); }'); 
        checkTestFunction('entity Foo { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} function main(): Bool { let x = Foo{3i}; return x.foo<Int>(); }'); 
    });

    it("should check simple entity methods with type template", function () {
        checkTestFunction('entity Foo<T> { field f: T; method foo(x: T): T { return if (true) then x else this.f; }} function main(): Int { let x = Foo<Int>{3i}; return x.foo(2i); }'); 
    });

    it("should check simple entity methods with both template", function () {
        checkTestFunction('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Nat>(); }'); 
        checkTestFunction('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Int>(); }'); 
    });

    it("should check simple entity methods with both template and more", function () {
        checkTestFunction('entity Foo<T> { field f: T; method foo<U>(u: U): U { return if (this.f)@<U> then $_ else u; }} function main(): Nat { let x = Foo<Int>{3i}; return x.foo<Nat>(3n); }'); 
        checkTestFunction('entity Foo<T> { field f: T; method foo<U>(t: T): T { return if (t)<U> then t else this.f; }} function main(): Int { let x = Foo<Int>{3i}; return x.foo<Int>(3i); }'); 
    });

    it("should check fail simple entity", function () {
        checkTestFunctionError('entity Foo { field f: Int; method foo(): Int { return this.f; }} function main(): Bool { let x = Foo{3i}; return x.foo(); }', "Expected a return value of type Bool but got Int");
        checkTestFunctionError('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} function main(): Int { return Foo{3i}.foo(); }', "Required argument x not provided"); 

        checkTestFunctionError('entity Foo<T> { field f: T; method foo<U>(t: T, u: U): U { return if (this.f)@<U> then $_ else t; }} function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Nat>(3n); }', "Argument t expected type Int but got Nat"); 
    });
});
