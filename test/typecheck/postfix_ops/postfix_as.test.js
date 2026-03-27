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

    it("should check postfix @ types", function () {
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Foo { return x@<Foo>; }");
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bar { return x@!<Foo>; }");

        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Foo { return x@<Foo>; }");
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Bar { return x@<Bar>; }");

        checkTestFunctionInFile("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } function main(x: Baz): Baz { return x@!<Foo>; }");
        checkTestFunctionInFile("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } function main(x: Baz): Bar { return x@<Bar>; }");
    });

    it("should check postfix @ types fail", function () {        
        checkTestFunctionInFileError("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } function main(x: Baz): Foo { return x@<Foo>; }", "Convert always fails");
    });

    it.skip("should check postfix @ types ADT", function () {
    });

    it.skip("should check postfix @ types ADT fail", function () {
    });
});
