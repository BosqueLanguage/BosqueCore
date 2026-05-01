"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Methods Pre/Post", () => {
    it("should exec simple entity methods", function () {
        runTestSet('entity Foo { field f: Int; method foo(): Int ensures $return > 0i; { return this.f; }} public function main(z: Int): Int { return Foo{z}.foo(); }', [['3i', '3i']], ['0i']); 
        runTestSet('entity Foo { field f: Int; method foo(): Int requires this.f > 0i; { return this.f; }} public function main(z: Int): Int { let x = Foo{z}; return x.foo(); }', [['3i', '3i']], ['0i']); 
    });
});
