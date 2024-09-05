"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Entity Constructor", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('entity Foo { } [FUNC]', 'function main(): Foo { return Foo{}; }');
        parseTestFunctionInFile('entity Foo { field f: Int; } [FUNC]', 'function main(): Foo { return Foo{1i}; }');
        parseTestFunctionInFile('entity Foo { field f: Int; field g: Bool; } [FUNC]', 'function main(): Foo { return Foo{1i, false}; }');
    });

    it("should parse nominal", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; } [FUNC]', 'function main(): Foo { return Foo{f = 1i}; }');
        parseTestFunctionInFile('entity Foo { field f: Int; field g: Bool; } [FUNC]', 'function main(): Foo { return Foo{g = true, 1i}; }');
    });

    it("should parse default", function () {
        parseTestFunctionInFile('entity Foo { field f: Int = 0i; } [FUNC]', 'function main(): Foo { return Foo{}; }');
    });

    it("should fail positional", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int; } function main(): Foo { return Foo(); }', 'Unexpected token in expression -- )');
    });

    it("should fail default", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int 0i; } function main(): Foo { return Foo{}; }', 'Expected ";" but got "0i" when parsing "member field"');
    });
});

describe ("Parser -- Entity w/ Invariants Constructor", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; invariant $f > 3i; } [FUNC]', 'function main(): Foo { return Foo{1i}; }');
        parseTestFunctionInFile('entity Foo { field f: Int; field g: Bool; invariant $g ==> $f > 3i; } [FUNC]', 'function main(): Foo { return Foo{1i, false}; }');
    });

    it("should fail missing semi", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int; invariant $f > 3i } function main(): Foo { return Foo{1i}; }', 'Expected ";" but got "}" when parsing "invariant"');
    });

    it("should fail missing names", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int; invariant f > 3i; } function main(): Foo { return Foo{1i}; }', "Could not resolve 'f' in this context");
    });
});
