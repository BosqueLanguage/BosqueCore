"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Type Alias Constructor", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('type Foo = Int; [FUNC]', 'function main(): Foo { return Foo{1i}; }');
    });

    it("should fail wrong parens or argc", function () {
        parseTestFunctionInFileError('type Foo = Int; function main(): Foo { return Foo(); }', 'Unknown type scoped expression');
    });
});

describe ("Parser -- Type Alias w/ Invariants Constructor", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('type Foo = Int & { invariant $value > 3i; } [FUNC]', 'function main(): Foo { return Foo{5i}; }');
    });

    it("should fail missing tokens", function () {
        parseTestFunctionInFile('type Foo = Int & { invariant $value > 3i }', 'Expected ";" but got "}" when parsing "invariant"');
        parseTestFunctionInFile('type Foo = Int  { invariant $value > 3i; }', 'Expected "," but got "invariant" when parsing "type declaration size range"');
        parseTestFunctionInFile('type Foo = Int &  invariant $value > 3i; }', 'Expected "{" but got "invariant" when parsing "type members"');
    });
});
