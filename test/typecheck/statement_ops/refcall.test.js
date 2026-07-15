"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- ref call statements", () => {
    it("should check ref call statements", function () {
        checkTestFunctionInFile('entity Foo { field x: Int; } function foo(ref z: Foo) { ; } public function main(): Int { ref z = Foo{3i}; foo(ref z); return z.x; }');
        checkTestFunctionInFile('entity Foo { field x: Int; ref method foo() { ; } } public function main(): Int { ref z = Foo{3i}; ref z.foo(); return z.x; }');
    });

    it("should fail ref call statements", function () {
        checkTestFunctionInFileError('entity Foo { field x: Int; } function foo(z: Foo) { return; } public function main(): Int { ref z = Foo{3i}; foo(z); return z.x; }', 'Call does not have any effect');
        checkTestFunctionInFileError('entity Foo { field x: Int; method foo(): Int { return 3i; } } public function main(): Int { ref z = Foo{3i}; z.foo(); return z.x; }', 'Call does not have any effect');
    });
});
