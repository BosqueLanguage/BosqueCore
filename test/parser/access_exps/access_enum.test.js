"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Access Enum Simple", () => {
    it("should parse enum lookup", function () {
        parseTestFunctionInFile('enum Foo {f1, F2, _f3} [FUNC]', 'function main(): Int { return Foo#f1; }');
        parseTestFunctionInFile('enum Foo {f1, F2, _f3} [FUNC]', 'function main(): Int { return Foo#F2; }');
        parseTestFunctionInFile('enum Foo {f1, F2, _f3} [FUNC]', 'function main(): Int { return Foo#_f3; }');
    });

    it("should fail bad decl", function () {
        parseTestFunctionInFileError('enum Foo {f1; F2; _f3} function main(): Int { return Foo::f1; }', 'Expected "}" but got "[RECOVER]" when parsing "enum members"');
        parseTestFunctionInFileError('enum Foo {f1, F2 _f3} function main(): Int { return Foo.f1; }', 'Expected "}" but got "[RECOVER]" when parsing "enum members"');
    });

    it("should fail bad :: vs # lookup", function () {
        parseTestFunctionInFileError('enum Foo {f1, F2, _f3} function main(): Int { return Foo::F1; }', 'Invalid identifier name -- must start with a lowercase letter or _');
        parseTestFunctionInFileError('enum Foo {f1, F2, _f3} function main(): Int { return Foo.f1; }', 'Unknown type scoped expression');
    });
});
