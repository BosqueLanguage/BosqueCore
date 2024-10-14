"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- entity decl", () => {
    it("should parse simple entity", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; } [FUNC]', 'function main(): Int { return Foo{3i}.f; }'); 
        parseTestFunctionInFile('entity Foo { field f: Int; invariant $f >= 0i; } [FUNC]', 'function main(): Int { return Foo{3i}.f; }'); 

        parseTestFunctionInFile('entity Foo<T> { field f: T; } [FUNC]', 'function main(): Int { return Foo<Int>{3i}.f; }'); 
    });

    it("should parse fail simple entity", function () {
        parseTestFunctionInFileError('entity Foo { f: Int; } function main(): Int { return Foo{3i}.f; }', "Unknown member f");

        parseTestFunctionInFileError('entity Foo { field f: Int; $f >= 0i; } function main(): Int { return Foo{3i}.f; }', "Unknown member $f");
    });
});

describe ("Parser -- entity decl with default fields", () => {
    it("should parse entity with default fields", function () {
        parseTestFunctionInFile('entity Foo { field f: Int = 3i; } [FUNC]', 'function main(): Int { return Foo{3i}.f; }'); 
        parseTestFunctionInFile('entity Foo { field f: Int; field g: Int = $f; } [FUNC]', 'function main(): Int { return Foo{3i}.g; }'); 
    });
});

describe ("Parser -- entity decl with consts", () => {
    it("should parse entity with consts", function () {
        parseTestFunctionInFile('entity Foo { const c: Int = 3i; } [FUNC]', 'function main(): Int { return Foo::c; }'); 
        parseTestFunctionInFile('entity Foo<T> { const c: Int = 3i; } [FUNC]', 'function main(): Int { return Foo.g; }'); 
    });

    it("should parse entity with consts errors", function () {
        parseTestFunctionInFileError('entity Foo { const c: Int; } function main(): Int { return Foo::c; }', "erro3"); 
        parseTestFunctionInFileError('entity Foo { const c = 3i; } function main(): Int { return Foo::c; }', "erro3"); 
    });
});

describe ("Parser -- entity decl with functions", () => {
    it("should parse entity with consts", function () {
        parseTestFunctionInFile('entity Foo { function foo(): Int { return 3i; } } [FUNC]', 'function main(): Int { return Foo::foo(); }');

        parseTestFunctionInFile('entity Foo<T> { function foo(x: T): T { return x; } } [FUNC]', 'function main(): Int { return Foo<Int>::foo(3i); }');
        parseTestFunctionInFile('entity Foo { function foo<T>(x: T): T { return x; } } [FUNC]', 'function main(): Int { return Foo::foo<Int>(3i); }');
    });
});

