"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- ref call statements", () => {
    it("should parse ref call statements", function () {
        parseTestFunctionInFile('entity Foo { field x: Int; ref method foo() { return; } } [FUNC]', 'function main(ref z: Foo): Int { ref z[x = 5i]; return this.x; }');
        parseTestFunctionInFile('entity Foo { field x: Int; ref method foo() { ref this[x = $x + 1i]; return; } } [FUNC]', 'function main(): Int { ref z = Foo{3i}; ref z.foo(); return z.x; }');
    });
});
