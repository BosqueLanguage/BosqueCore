"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- entity is/as", () => {
    it("should check postfix @ option", function () {
        checkTestFunctionInFile("function main(x: Option<Int>): None { return x@none; }");
        checkTestFunctionInFile("function main(x: Option<Int>): Int { return x@!none; }");

        checkTestFunctionInFile("function main(x: Option<Int>): Int { return x@some; }");
        checkTestFunctionInFile("function main(x: Option<Int>): None { return x@!some; }");
    });

    it("should check postfix @ option fail", function () {
        checkTestFunctionInFileError("function main(x: Some<Int>): None { return x@none; }", "Convert always fails");
        checkTestFunctionInFileError("function main(x: Some<Int>): None { return x@!some; }", "Convert always fails");

        checkTestFunctionInFileError("function main(x: None): Some<Int> { return x@some; }", "Convert always fails");
        checkTestFunctionInFileError("function main(x: None): Some<Int> { return x@!none; }", "Convert always fails");
    });

    /*
    it("should check  simple entity is", function () {
        checkTestFunctionInFile('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Bar>; }');
    });

    it("should check (error) simple entity is", function () {
        checkTestFunctionInFileError('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { return Bar{3i}?<Bar>; }', "Test is never false");

        checkTestFunctionInFileError('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { return Bar{3i}?<Foo>; }', "Test is never false");
    });
    */
});
