"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Entity Constructor", () => {
    it("should parse positional", function () {
        parseTestFunctionInFile('entity Foo { } [FUNC]', 'function main(): Foo { return Foo{}; }');
        parseTestFunctionInFile('entity Foo { field f: Int; } [FUNC]', 'function main(): Foo { return Foo{1i}; }');
        parseTestFunctionInFile('entity Foo { field f: Int; field g: Bool; } [FUNC]', 'function main(): Foo { return Foo{1i, false}; }');
    });

    it("should fail positional", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int; } function main(): Foo { return Foo(); }', 'Unexpected token in expression -- )');
    });
});
