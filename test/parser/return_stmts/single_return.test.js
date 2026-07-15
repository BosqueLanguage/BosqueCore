"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- simple return", () => {
    it("should parse simple returns", function () {
        parseTestFunctionInFile('[FUNC]', 'function main(): Int { return 2i; }');
        parseTestFunctionInFile('[FUNC]', 'function main() { return; }');
    });
});

describe ("Parser -- return with refs", () => {
    it("should parse return with refs", function () {
        parseTestFunctionInFile("function foo(out y: Int): Int { return 1i; } [FUNC]", "function main(): Int { var y: Int; return foo(out y); }", undefined);
        parseTestFunctionInFile("entity Foo { ref method foo() { ; } } [FUNC]", "function main(): Int { let z = Foo{}; return ref z.foo(); }", undefined);
    });
});