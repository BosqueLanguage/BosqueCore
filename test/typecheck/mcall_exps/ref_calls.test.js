"use strict";

import { checkTestFunctionInFile, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- entity ref methods", () => {
    it("should check simple entity ref methods", function () {
        checkTestFunctionInFile('entity Foo { field f: Int; ref method foo(): Int { return this.f; }} public function main(): Int { var x = Foo{3i}; return ref x.foo(); }'); 

        checkTestFunctionInFile('entity Foo { field f: Int; ref method foo(): Int { ref this[f = 1i]; return this.f; }} public function main(): Int { var x = Foo{3i}; return ref x.foo(); }'); 
    });

    it("should check fail simple ref entity", function () {
        checkTestFunctionInFileError('entity Foo { field f: Int; method foo(x: Int): Int { return this.f + x; }} public function main(): Int { var v = Foo{3i}; return ref v.foo(1i); }', 'Method foo is not a "ref" method and cannot be called with a ref rcvr'); 
        checkTestFunctionInFileError('entity Foo { field f: Int; ref method foo(x: Int): Int { return this.f + x; }} public function main(): Int { var v = Foo{3i}; return v.foo(1i); }', 'Method foo is a "ref" method and cannot be called without a ref rcvr'); 
    });
});

describe ("Checker -- eADT ref methods", () => {
    it("should check simple eADT ref methods", function () {
        checkTestFunctionInFile('datatype Foo of Foo1 { field f: Int; ref method foo(x: Int): Int { return this.f + x; }} ; public function main(): Int { var x = Foo1{3i}; return ref x.foo(1i); }'); 
    });
});
