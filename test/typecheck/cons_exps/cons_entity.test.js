"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Entity Constructor", () => {
    it("should check positional", function () {
        checkTestFunctionInFile('entity Foo { } [FUNC]', 'function main(): Foo { return Foo{}; }');
        checkTestFunctionInFile('entity Foo { field f: Int; } [FUNC]', 'function main(): Foo { return Foo{1i}; }');
        checkTestFunctionInFile('entity Foo { field f: Int; field g: Bool; } [FUNC]', 'function main(): Foo { return Foo{1i, false}; }');
    });

    it("should fail positional", function () {
        checkTestFunctionInFileError('entity Foo { field f: Int; } function main(): Foo { return Foo{}; }', 'err1');
    });
});
