"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- entity methods", () => {
    it("should parse simple entity methods", function () {
        parseTestFunctionInFile('entity Foo { field f: Int; method foo(): Int ensures $return > 0i; { return this.f; }} [FUNC]', 'function main(): Int { return Foo{3i}.foo(); }'); 
        parseTestFunctionInFile('entity Foo { field f: Int; method foo(): Int requires this.f > 0i; { return this.f; }} [FUNC]', 'function main(): Int { let x = Foo{3i}; return x.foo(); }'); 
    });
});

