"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- ref call statements", () => {
    it("should exec ref call statements", function () {
        runTestSet('entity Foo { field x: Int; } function foo(ref z: Foo) { ref z[x = $x + 1i]; } public function main(i: Int): Int { ref z = Foo{i}; foo(ref z); return z.x; }', [['3i', '4i']], []);
        runTestSet('entity Foo { field x: Int; ref method foo() { ref this[x = $x + 1i]; } } public function main(i: Int): Int { ref z = Foo{i}; ref z.foo(); return z.x; }', [['3i', '4i']], []);
    });
});
