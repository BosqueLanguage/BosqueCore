"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Type Alias Constructor", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('type Foo = Int; [FUNC]', 'function main(): Int { return Foo{1i}.value; }');
    });

    it("should fail positional", function () {
        parseTestFunctionInFileError('type Foo = Int; function main(): Foo { return Foo(); }', 'Unknown type scoped expression');
    });
});

describe ("Parser -- Type Alias w/ Invariants Constructor", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('type Foo = Int & { invariant $value > 3i; } [FUNC]', 'function main(): Foo { return Foo{5i}; }');
    });

    it("should fail missing tokens", function () {
        parseTestFunctionInFile('type Foo = Int & { invariant $value > 3i } [FUNC]', 'Expected ";" but got "}" when parsing "invariant"');
        parseTestFunctionInFile('type Foo = Int  { invariant $value > 3i; } [FUNC]', 'Expected "&" but got "{" when parsing "type declaration"');
        parseTestFunctionInFile('type Foo = Int &  invariant $value > 3i; } [FUNC]', 'Expected "{" but got "invariant" when parsing "type members"');
    });

    it("should fail missing names", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int; invariant value > 3i; } function main(): Foo { return Foo{1i}; }', "Could not resolve 'value' in this context");
    });
});
