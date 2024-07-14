"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- StringOf", () => {
    it("should parse simple stringof", function () {
        parseTestFunctionInFile('validator Foo = /[0-9]*/; [FUNC]', 'function main(): StringOf<Foo> { return ""_Foo; }');
        parseTestFunctionInFile('validator Foo = /[0-9]*/; [FUNC]', 'function main(): StringOf<Foo> { return "123"_Foo; }');
        parseTestFunctionInFile('validator Foo = /[0-9]*/; [FUNC]', 'function main(): StringOf<Foo> { return "a🌵c"_Foo; }');
    });

    it("should fail missing under", function () {
        parseTestExpError('"abc"Foo', 'Expected ";" but got "Foo" when parsing "line statement"', "StringOf<Foo>");
    });

    it("should fail missing typename", function () {
        parseTestExpError('"abc"_', 'err2', "StringOf<Foo>");
    });
});

describe ("Parser -- CStringOf", () => {
    it("should parse simple cstringof", function () {
        parseTestFunctionInFile('validator Foo = /[0-9]*/; [FUNC]', "function main(): CStringOf<Foo> { return ''_Foo; }");
        parseTestFunctionInFile('validator Foo = /[0-9]*/; [FUNC]', "function main(): CStringOf<Foo> { return '123'_Foo; }");
    });

    it("should fail missing under", function () {
        parseTestExpError("'abc'Foo", 'Expected ";" but got "Foo" when parsing "line statement"', "CStringOf<Foo>");
    });
});