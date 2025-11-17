"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- entity is/as", () => {
    it("should check  simple entity is", function () {
        checkTestFunctionInFile('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Bar>; }');
    });

    it("should check (error) simple entity is", function () {
        checkTestFunctionInFileError('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { return Bar{3i}?<Bar>; }', "Test is never false");

        checkTestFunctionInFileError('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { return Bar{3i}?<Foo>; }', "Test is never false");
    });
});
