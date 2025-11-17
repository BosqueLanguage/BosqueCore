"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- entity methods", () => {
    it("should parse simple entity methods", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; method foo(): Int { return this.f; }} [FUNC]', 'function main(): Int { return Foo{3i}.foo(); }'); 
        parseTestFunctionInFile('entity Foo { field f: Int; method foo(): Int { return this.f; }} [FUNC]', 'function main(): Int { let x = Foo{3i}; return x.foo(); }'); 
    });

    it("should parse simple entity methods with args", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} [FUNC]', 'function main(): Int { return Foo{3i}.foo(1i); }'); 
        parseTestFunctionInFile('entity Foo { field f: Int; method foo(x: Int = 1i): Int { return this.f + x; }} [FUNC]', 'function main(): Int { let x = Foo{3i}; return x.foo(); }'); 
    });

    it("should parse simple entity methods with template", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} [FUNC]', 'function main(): Bool { let x = Foo{3i}; return x.foo<Nat>(); }'); 
        parseTestFunctionInFile('entity Foo { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} [FUNC]', 'function main(): Bool { let x = Foo{3i}; return x.foo<Int>(); }'); 
    });

    it("should parse simple entity methods with both template", function () {
        parseTestFunctionInFile('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} [FUNC]', 'function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Nat>(); }'); 
        parseTestFunctionInFile('entity Foo<T> { field f: T; method foo<U>(): Bool { return this.f?<U>; }} [FUNC]', 'function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Int>(); }'); 
    });

    it("should parse simple entity methods with both template and more", function () {
        parseTestFunctionInFile('entity Foo<T> { field f: T; method foo<U>(t: T, u: U): U { return if (this.f)@<U> then $_ else u; }} [FUNC]', 'function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Nat>(3n); }'); 
        parseTestFunctionInFile('entity Foo<T> { field f: T; method foo<U>(t: T, u: U): U { return if (this.f)@<U> then $_ else u; }} [FUNC]', 'function main(): Bool { let x = Foo<Int>{3i}; return x.foo<Int>(3i); }'); 
    });

    it("should parse fail simple entity", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int; foo(): Bool { return this.f; }} function main(): Bool { let x = Foo{3i}; return x.foo(); }', "Unknown member foo");
        parseTestFunctionInFileError('entity Foo { field f: Int; method foo(): Bool { return this.f; }} function main(): Bool { let x = Foo{3i}; return x..foo(); }', 'Expected "[IDENTIFIER]" but got "." when parsing "postfix access/invoke"');
        parseTestFunctionInFileError('entity Foo { field f: Int; method foo(): Bool { return this.f; }} function main(): Bool { let x = Foo{3i}; return x->foo(); }', "Unrecognized token");
    });
});

describe ("Parser -- eADT methods", () => {
    it("should parse simple eADT methods", function () {
        parseTestFunctionInFile('datatype Foo of | Foo1 { field f: Int; method foo(): Int { return this.f; }} ; [FUNC]', 'function main(): Int { return Foo1{3i}.foo(); }'); 
        parseTestFunctionInFile('datatype Foo of | Foo1 { field f: Int; method foo(x: Int): Int { return this.f + x; }} ; [FUNC]', 'function main(): Int { return Foo1{3i}.foo(1i); }'); 
    });

    it("should parse simple eADT methods with template", function () {
        parseTestFunctionInFile('datatype Foo of | Foo1 { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} ; [FUNC]', 'function main(): Bool { let x = Foo1{3i}; return x.foo<Nat>(); }'); 
        parseTestFunctionInFile('datatype Foo of | Foo1 { field f: Int; method foo<T>(): Bool { return this.f?<T>; }} ; [FUNC]', 'function main(): Bool { let x = Foo1{3i}; return x.foo<Int>(); }'); 
    });

    it("should parse simple eADT methods with type template", function () {
        parseTestFunctionInFile('datatype Foo<T> of | Foo1 { field f: T; method foo(x: T): T { return if (true) then x else this.f; }} ; [FUNC]', 'function main(): Int { let x = Foo1<Int>{3i}; return x.foo(2i); }'); 
    });
});

describe ("parser -- type alias methods", () => {
    it("should parse simple type alias methods", function () {
        parseTestFunctionInFile('type Foo = Int & { method foo(): Int { return this.value; }} [FUNC]', 'function main(): Int { return 3i<Foo>.foo(); }'); 
        parseTestFunctionInFile('type Foo = Int & { method foo(x: Int): Int { return this.value + x; }} [FUNC]', 'function main(): Int { return 3i<Foo>.foo(1i); }'); 
    });

    it("should parse simple type alias methods with template", function () {
        parseTestFunctionInFile('type Foo = Int & { method foo<T>(): Bool { return this.value?<T>; }} [FUNC]', 'function main(): Bool { let x = 3i<Foo>; return x.foo<Nat>(); }'); 
        parseTestFunctionInFile('type Foo = Int & { method foo<T>(): Bool { return this.value?<T>; }} [FUNC]', 'function main(): Bool { let x = 3i<Foo>; return x.foo<Int>(); }'); 
    });
});
