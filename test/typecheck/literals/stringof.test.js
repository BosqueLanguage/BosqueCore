"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe("Checker -- StringOf", () => {
    it("should check simple stringof", function () {
        checkTestFunctionInFile('validator Foo = /[0-9]*/; function main(): StringOf<Foo> { return ""_Foo; }');
        checkTestFunctionInFile('validator Foo = /[0-9]*/; function main(): StringOf<Foo> { return "123"_Foo; }');
    });

    it("should check simple stringof fails", function () {
        checkTestFunctionInFileError('validator Foo = /[0-9]*/; function main(): StringOf<Foo> { return "a"_Foo; }', "Literal value does not match regex validator Main::Foo");
        checkTestFunctionInFileError('validator Foo = /[0-9]+/; function main(): StringOf<Foo> { return ""_Foo; }', "Literal value does not match regex validator Main::Foo");
        checkTestFunctionInFileError('validator Foo = /[0-9]*/; function main(): StringOf<Foo> { return "a🌵c"_Foo; }', "Literal value does not match regex validator Main::Foo");
    });

    it("should fail mismatch regex", function () {
        checkTestFunctionInFileError('validator Foo = /[0-9]*/c; function main(): StringOf<Foo> { return "123"_Foo; }', "Template argument T is not a subtype of RegexValidator");
    });

    it("should fail missing typename", function () {
        checkTestFunctionInFileError('validator Foo = /[0-9]*/; function main(): StringOf<Foo> { return "123"; }', "Expected a return value of type StringOf<Foo> but got String");
    });
});

describe("Checker -- CStringOf", () => {
    it("should check simple cstringof", function () {
        checkTestFunctionInFile("validator Foo = /[0-9]*/c; function main(): CStringOf<Foo> { return ''_Foo; }");
        checkTestFunctionInFile("validator Foo = /[0-9]*/c; function main(): CStringOf<Foo> { return '123'_Foo; }");
    });

    it("should check simple cstringof fails", function () {
        checkTestFunctionInFileError("validator Foo = /[0-9]+/c; function main(): CStringOf<Foo> { return ''_Foo; }", "Literal value does not match regex validator Main::Foo");
        checkTestFunctionInFileError("validator Foo = /[0-9]*/c; function main(): CStringOf<Foo> { return 'a'_Foo; }", "Literal value does not match regex validator Main::Foo");
    });

    it("should fail mismatch regex", function () {
        checkTestFunctionInFileError("validator Foo = /[0-9]*/; function main(): CStringOf<Foo> { return '123'_Foo; }", "Template argument T is not a subtype of CRegexValidator");
    });

    it("should fail missing typename", function () {
        checkTestFunctionInFileError("validator Foo = /[0-9]*/c; function main(): CStringOf<Foo> { return '123'; }", "Expected a return value of type CStringOf<Foo> but got CString");
    });
});
