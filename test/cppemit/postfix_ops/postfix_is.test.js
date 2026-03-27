"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- entity is", () => {
    it("should emit postfix ? option", function () {
        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?none; }", "Bool Mainᕒmain(OptionᐸIntᐳ x) { return x.isNone(); }");
        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?!none; }", "bbb");

        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?some; }", "ccc");
        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?!some; }", "ddd");

        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?<None>; }", "fff");
        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?<Some<Int>>; }", "ggg");
    });

    /*
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
    */
    it("should check postfix ? types", function () {
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x?<Foo>; }", "ppp");
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x?!<Foo>; }", "qqq");
    });
    /*
    it("should check postfix ? types fail", function () {
        checkTestFunctionInFileError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Bool { return x?<Foo>; }", "Test is never false");
        checkTestFunctionInFileError("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } function main(x: Baz): Bool { return x?!<Foo>; }", "Test is never false");

        checkTestFunctionInFileError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Bool { return x?!<Foo>; }", "Test is never true");
        checkTestFunctionInFileError("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } function main(x: Baz): Bool { return x?<Foo>; }", "Test is never true");
    });
    */
});
