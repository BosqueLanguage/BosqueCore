"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- entity is/as", () => {
    it("should check postfix ? option", function () {
        checkTestFunctionInFile("function main(x: Option<Int>): Bool { return x?none; }");
        checkTestFunctionInFile("function main(x: Option<Int>): Bool { return x?!none; }");

        checkTestFunctionInFile("function main(x: Option<Int>): Bool { return x?some; }");
        checkTestFunctionInFile("function main(x: Option<Int>): Bool { return x?!some; }");
    });

    it("should check postfix ? option fail", function () {
        checkTestFunctionInFileError("function main(x: Some<Int>): Bool { return x?none; }", "Test is never true");
        checkTestFunctionInFileError("function main(x: Some<Int>): Bool { return x?!none; }", "Test is never false");

        checkTestFunctionInFileError("function main(x: Some<Int>): Bool { return x?!some; }", "Test is never true");
        checkTestFunctionInFileError("function main(x: Some<Int>): Bool { return x?some; }", "Test is never false");

        checkTestFunctionInFileError("function main(x: None): Bool { return x?none; }", "Test is never false");
        checkTestFunctionInFileError("function main(x: None): Bool { return x?!none; }", "Test is never true");

        checkTestFunctionInFileError("function main(x: None): Bool { return x?!some; }", "Test is never false");
        checkTestFunctionInFileError("function main(x: None): Bool { return x?some; }", "Test is never true");
    });

    it("should check postfix ? types", function () {
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x?<Foo>; }");
        checkTestFunctionInFile("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x?!<Foo>; }");
    });

    it("should check postfix ? types fail", function () {
        checkTestFunctionInFileError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Bool { return x?<Foo>; }", "Test is never false");
        checkTestFunctionInFileError("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } function main(x: Baz): Bool { return x?!<Foo>; }", "Test is never false");

        checkTestFunctionInFileError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Bool { return x?!<Foo>; }", "Test is never true");
        checkTestFunctionInFileError("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } function main(x: Baz): Bool { return x?<Foo>; }", "Test is never true");
    });
});
