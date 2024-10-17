"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Entity Simple", () => {
    it("should check simple entity", function () {
        checkTestFunctionInFile('entity Foo { field f: Int; } function main(): Int { return Foo{3i}.f; }'); 
        checkTestFunctionInFile('entity Foo { field f: Int; invariant $f >= 0i; } function main(): Int { return Foo{3i}.f; }'); 

        checkTestFunctionInFile('entity Foo<T> { field f: T; } function main(): Int { return Foo<Int>{3i}.f; }'); 
    });

    it("should check fail simple entity", function () {
        checkTestFunctionInFileError('entity Foo { field f: Int; } function main(): Int { return Foo{3i}.g; }', "Could not find field g in type Foo");

        checkTestFunctionInFileError('entity Foo { field f: Int; invariant $f >= 0i; } function main(): Nat { return Foo{3i}.f; }', "Expected a return value of type Nat but got Int");
        checkTestFunctionInFileError('entity Foo { field f: Int; invariant $f >= 0n; } function main(): Int { return Foo{3i}.f; }', "Operator >= requires 2 arguments of the same type");
    });
});

describe ("Checker -- entity decl with default fields", () => {
    it("should check entity with default fields", function () {
        checkTestFunctionInFile('entity Foo { field f: Int = 3i; } function main(): Int { return Foo{3i}.f; }'); 
        checkTestFunctionInFile('entity Foo { field f: Int = 3i; } function main(): Int { return Foo{}.f; }'); 

        checkTestFunctionInFile('entity Foo { field f: Int; field g: Int = $f; } function main(): Int { return Foo{3i}.g; }'); 
    });

    it("should check fail entity with default fields", function () {
        checkTestFunctionInFileError('entity Foo { field f: Int = 3n; } function main(): Int { return Foo{3i}.f; }', "Field initializer does not match declared type -- expected Int but got Nat");

        checkTestFunctionInFileError('entity Foo { field f: Int; field g: Nat = $f; } function main(): Nat { return Foo{3i}.g; }', "Field initializer does not match declared type -- expected Nat but got Int");
    });
});

describe ("Checker -- entity decl with consts", () => {
    it("should check entity with consts", function () {
        checkTestFunctionInFile('entity Foo { const c: Int = 3i; } function main(): Int { return Foo::c; }'); 
        checkTestFunctionInFile('entity Foo<T> { const c: Int = 3i; } function main(): Int { return Foo<Nat>::c; }'); 
    });

    it("should check entity with consts errors", function () {
        checkTestFunctionInFileError('entity Foo { const c: Int = 3i; } function main(): Nat { return Foo::c; }', "Expected a return value of type Nat but got Int"); 
        checkTestFunctionInFileError('entity Foo<T> { const c: Int = 3n; } function main(): Int { return Foo<Nat>::c; }', "xerro4"); 
    });
});

describe ("Checker -- entity decl with functions", () => {
    it("should check entity with consts", function () {
        checkTestFunctionInFile('entity Foo { function foo(): Int { return 3i; } } function main(): Int { return Foo::foo(); }');

        checkTestFunctionInFile('entity Foo<T> { function foo(x: T): T { return x; } } function main(): Int { return Foo<Int>::foo(3i); }');
        checkTestFunctionInFile('entity Foo { function foo<T>(x: T): T { return x; } } function main(): Int { return Foo::foo<Int>(3i); }');
    });
});