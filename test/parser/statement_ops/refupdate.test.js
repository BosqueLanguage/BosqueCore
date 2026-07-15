"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- ref updates", () => {
    it("should parse ref updates", function () {
        parseTestFunctionInFile('entity Foo { field x: Int; } [FUNC]', 'function main(ref z: Foo): Int { ref z[x = 5i]; return this.x; }');
        parseTestFunctionInFile('entity Foo { field x: Int; } [FUNC]', 'function main(ref z: Foo): Int { ref z[x = $x + 1i]; return this.x; }');
    });

    it("should fail ref updates", function () {
        parseTestFunctionInFileError('entity Foo { field x: Int; } function foo(ref z: Foo): Int { z[x = 5i]; return this.x; }', 'Expected a call expression');
        parseTestFunctionInFileError('entity Foo { field x: Int; } function ref foo(): Int { ref this[x: 5i]; return this.x; }', 'Expected "[IDENTIFIER]" but got "ref" when parsing "function name"');

        parseTestFunctionInFileError('entity Foo { field x: Int; } function foo(ref z: Foo): Int { ref z[x = 5i; return this.x; }', 'Expected "]" but got "[RECOVER]" when parsing "variable update list"');
        parseTestFunctionInFileError('entity Foo { field x: Int; } function foo(ref z: Foo): Int { ref z.[x = 5i]; return this.x; }', 'Expected "[IDENTIFIER]" but got "[" when parsing "ref invoke"');

        parseTestFunctionInFileError('entity Foo { field x: Int; } function foo(ref z: Foo): Int { ref z[]; return this.x; }', 'Empty update list is not allowed');
    });
});
