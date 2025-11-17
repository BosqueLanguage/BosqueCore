"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- simple field updates", () => {
    it("should check simple field updates", function () {
        checkTestFunctionInFile('entity Foo{ field x: Int; } public function main(): Int { var v = Foo{1i}; return v[x = 2i].x;}');
        checkTestFunctionInFile('entity Foo{ field x: Int; } public function main(): Int { var v = Foo{1i}; return v[x = $x + 1i].x; }');
    });

    it("should check simple field updates (fail)", function () {
        checkTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { var v = Foo{1i}; return v[x = 2n].x; }', 'Expression of type Nat cannot be assigned to field x of type Int');
        checkTestFunctionInFileError('entity Foo{ field x: Int; } function main(): Int { var v = Foo{1i}; return v[y = 2i].x; }', 'Field y is not a member of type Foo');
    });

    it("should check postfix field updates", function () {
        checkTestFunctionInFile('entity Foo { field x: Int; field y: Int; } entity Bar { field f: Foo; } function main(): Int { let a = Bar{Foo{1i, 0i}}; let b = a.f[x=3i]; return b.x; }');
    });
});

