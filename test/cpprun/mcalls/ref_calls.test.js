"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- entity ref methods", () => {
    it("should exec simple entity ref methods", function () {
        runTestSet('entity Foo { field f: Int; ref method foo(): Int { return this.f; }} public function main(y: Int): Int { var x = Foo{y}; return ref x.foo(); }', [['3i', '3i']], []); 
    });
});

describe ("CPPExec -- eADT ref methods", () => {
    it("should exec simple eADT ref methods", function () {
        runTestSet('datatype Foo of Foo1 { field f: Int; ref method foo(x: Int): Int { return this.f + x; }} ; public function main(y: Int): Int { var x = Foo1{y}; return ref x.foo(1i); }', [['3i', '4i']], []); 
    });
});
