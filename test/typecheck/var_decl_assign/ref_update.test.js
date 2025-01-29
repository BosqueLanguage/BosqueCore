"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- simple ref updates", () => {
    it("should check simple ref updates", function () {
        checkTestFunctionInFile('entity Foo{ field x: Int; } public function main(): Int { var v = Foo{1i}; ref v[x = 2i]; return v.x; }');
        checkTestFunctionInFile('entity Foo{ field x: Int; } public function main(): Int { var v = Foo{1i}; ref v[x = $x + 1i]; return v.x; }');
    });

    it("should parse simple ref updates (fail)", function () {
        checkTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { var v = Foo{1i}; ref v[x = 2n]; return v.x; }', 'Expression of type Nat cannot be assigned to field x of type Int');
        checkTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { var v = Foo{1i}; ref v[y = 2i]; return v.x; }', 'Field y is not a member of type Foo');

        checkTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { let v = Foo{1i}; ref v[y = 2i]; return v.x; }', 'Variable v is cannot be updated (is local const or not a ref param)');
    });
});

