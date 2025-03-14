"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- simple field updates", () => {
    it("should parse simple field updates", function () {
        parseTestFunctionInFile('entity Foo{ field x: Int; } [FUNC]', 'function main(): Int { var v = Foo{1i}; return v[x = 2i].x; }');
        parseTestFunctionInFile('entity Foo{ field x: Int; } [FUNC]', 'function main(): Int { var v = Foo{1i}; return v[x = $x + 1i].x; }');
    });

    it("should parse simple field updates (fail)", function () {
        parseTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { var v = Foo{1i}; v[x 2i].x; }', 'Expected "=" but got "2i" when parsing "variable update list"');
        parseTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { var v = Foo{1i}; v[x] = 2i; return v.x; }', 'Expected "=" but got "]" when parsing "variable update list"');
    });
});

