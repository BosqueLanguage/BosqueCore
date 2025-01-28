"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- simple ref updates", () => {
    it("should parse simple ref updates", function () {
        parseTestFunctionInFile('entity Foo{ field x: Int; } [FUNC]', 'function main(): Int { var v = Foo{1i}; ref v[x = 2i]; return v.x; }');
        parseTestFunctionInFile('entity Foo{ field x: Int; } [FUNC]', 'function main(): Int { var v = Foo{1i}; ref v[x = $x + 1i]; return v.x; }');
    });

    it("should parse simple ref updates (fail)", function () {
        parseTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { var v = Foo{1i}; ref v[x 2i]; return v.x; }');
        parseTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { var v = Foo{1i}; ref v[x] = 2i; return v.x; }');
    });
});

