"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Entity Methods", () => {
    it("should check simple entity methods", function () {
        checkTestFunctionInFile('entity Foo { field f: Int; method foo(): Int ensures $return > 0i; { return this.f; }} function main(): Int { return Foo{3i}.foo(); }'); 
        checkTestFunctionInFile('entity Foo { field f: Int; method foo(): Int requires this.f > 0i; { return this.f; }} function main(): Int { let x = Foo{3i}; return x.foo(); }'); 
    });

    it("should check simple entity methods -- fail", function () {
        checkTestFunctionInFileError('entity Foo { field f: Int; method foo(): Int ensures $return; { return this.f; }} function main(): Int { return Foo{3i}.foo(); }', 'Ensures expression does not have a boolean type -- got Int'); 
        checkTestFunctionInFileError('entity Foo { field f: Int; method foo(): Int requires this.g > 0i; { return this.f; }} function main(): Int { let x = Foo{3i}; return x.foo(); }', 'Could not find field g in type Main::Foo'); 
    });
});

