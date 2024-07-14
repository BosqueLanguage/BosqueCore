"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- StringOf", () => {
    it("should parse simple stringof", function () {
        parseTestFunctionInFile('validator Foo = /[0-9]*/; [FUNC]', 'function main(): StringOf<Foo> { return ""_Foo; }');
        parseTestFunctionInFile('validator Foo = /[0-9]*/; [FUNC]', 'function main(): StringOf<Foo> { return "123"_Foo; }');
        parseTestFunctionInFile('validator Foo = /[0-9]*/; [FUNC]', 'function main(): StringOf<Foo> { return "a🌵c"_Foo; }');
    });

    it("should fail missing under", function () {
        parseTestFunctionInFileError('validator Foo = /[0-9]*/; function main(): StringOf<Foo> { return "123"Foo; }', 'Expected ";" but got "Foo" when parsing "line statement"');
    });
});

describe ("Parser -- CStringOf", () => {
    it("should parse simple cstringof", function () {
        parseTestFunctionInFile("validator Foo = /[0-9]*/c; [FUNC]", "function main(): CStringOf<Foo> { return ''_Foo; }");
        parseTestFunctionInFile("validator Foo = /[0-9]*/c; [FUNC]", "function main(): CStringOf<Foo> { return '123'_Foo; }");
    });

    it("should fail missing under", function () {
        parseTestFunctionInFileError("validator Foo = /[0-9]*/c; function main(): StringOf<Foo> { return '123'Foo; }", 'Expected ";" but got "Foo" when parsing "line statement"');
    });
});