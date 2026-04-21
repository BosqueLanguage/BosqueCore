"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Postfix Chains", () => {
    it("should parse simple postfix chains", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; } entity Bar { field g: Foo; } [FUNC]', 'function main(): Int { return Bar{Foo{3i}}.g.f; }'); 
        parseTestFunctionInFile('type Bar = Int; entity Foo { field f: Bar; } [FUNC]', 'function main(): Int { let x = Foo{Bar{3i}}; return x.f.value; }'); 
    });
});
