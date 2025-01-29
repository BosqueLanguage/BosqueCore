"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- entity ref methods", () => {
    it("should parse simple entity methods", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; ref method foo(): Int { return this.f; }} [FUNC]', 'function main(): Int { return ref this.foo(); }'); 
        parseTestFunctionInFile('entity Foo { field f: Int; ref method foo(): Int { return this.f; }} [FUNC]', 'function main(): Int { let x = Foo{3i}; return ref x.foo(); }'); 
    });

    it("should parse fail simple ref entity", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} function main(): Int { return ref Foo{3i}.foo(1i); }', 'Expected "." but got "{" when parsing "ref invoke"'); 
        parseTestFunctionInFileError('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} function main(): Int { return ref this.foo(ref that); }', 'Cannot have a reference argument in this context'); 
    });
});

describe ("Parser -- eADT ref methods", () => {
    it("should parse simple eADT methods", function () {
        parseTestFunctionInFile('datatype Foo of Foo1 { field f: Int; method foo(x: Int): Int { return this.f + x; }} ; [FUNC]', 'function main(): Int { let x = Foo{3i}; return ref x.foo(1i); }'); 
    });
});
