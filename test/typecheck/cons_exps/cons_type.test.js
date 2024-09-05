"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Type Alias Constructor", () => {
    it("should check positional", function () {
        checkTestFunctionInFile('type Foo = Int; function main(): Int { return Foo{1i}.value; }');
    });

    it("should fail positional", function () {
        checkTestFunctionInFileError('type Foo = Int; function main(): Foo { return Foo{}.value; }', 'Foo constructor expects 1 argument');
        checkTestFunctionInFileError('type Foo = Int; function main(): Foo { return Foo{1i, 2i}.value; }', 'err222');
    });

    it("should fail type", function () {
        checkTestFunctionInFileError('type Foo = Int; function main(): Foo { return Foo{2n}.value; }', 'Nat constructor argument is not a compatible with Int');
    });
});


describe ("Checker -- Type Alias w/ Invariant Constructor", () => {
    it("should check positional", function () {
        checkTestFunctionInFile('type Foo = Int & { invariant $value > 3i; } function main(): Foo { return Foo{1i}; }');
    });

    it("should fail missing names", function () {
        checkTestFunctionInFileError('type Foo = Int & { invariant $g > 3i; } function main(): Foo { return Foo{1i}; }', 'Variable $g is not declared here');
    });

    it("should fail bool", function () {
        checkTestFunctionInFileError('type Foo = Int & { invariant $value; } function main(): Foo { return Foo{3i}; }', 'Invariant expression does not have a boolean type -- got Int');
    });
});
