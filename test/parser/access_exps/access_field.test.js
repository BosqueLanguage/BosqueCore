"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Access Field Simple", () => {
    it("should parse non-virtual lookup", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; } [FUNC]', 'function main(x: Foo): Int { return x.f; }');
        parseTestFunctionInFile('entity Foo { field f: Int; } function foo(): Foo { return Foo{1i}; } [FUNC]', 'function main(): Int { return foo().f; }');
    });

    it("should fail non-virtual lookup", function () {
        parseTestFunctionInFileError('entity Foo { field f: Int; } function main(x: Foo): Int { return x..; }', 'Expected "[IDENTIFIER]" but got "." when parsing "postfix access/invoke"');
    });
});

