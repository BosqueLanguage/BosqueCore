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
        runMainCode('entity Foo { field f: Int; method foo(x: Int = 1i): Int { return this.f + x; }} public function main(): Int { let x = Foo{3i}; return x.foo(); }', "4_i"); 
    });

    it("should exec simple entity methods with named args", function () {
        runMainCode('entity Foo { field f: Int; method foo(x: Int, y: Int): Int { return this.f + x + y; }} public function main(): Int { return Foo{3i}.foo(x=1i,y=2i); }', "6_i"); 
    });

    // Will need to add more comprehensive testing here
    it("should exec simple entity methods with template args", function () {
        runMainCode('entity Foo { method foo<T>(x: T, y: T): T { return y; }} public function main(): Int { return Foo{}.foo<Int>(1i, 2i); }', "2_i");
    });
    it("should exec simple entity methods with multiple template args", function () {
        runMainCode('entity Foo { method foo<T, K>(x: T, y: K): T { return x; }} public function main(): Int { return Foo{}.foo<Int, Nat>(2i, 1n); }', "2_i");
    });
});