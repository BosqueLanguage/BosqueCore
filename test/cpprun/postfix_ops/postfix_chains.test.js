"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Postfix Chains", () => {
    it("should exec simple postfix chains", function () {
        runTestSet('entity Foo { field f: Int; } entity Bar { field g: Foo; } public function main(b: Bar): Int { return b.g.f; }', [['Main::Bar{Main::Foo{3i}}', '3i']], []);
        runTestSet('type Bar = Int; entity Foo { field f: Bar; } public function main(z: Int): Int { let x = Foo{Bar{z}}; return x.f.value; }', [['3i', '3i']], []);

        runTestSet('entity Foo { method f(x: Int): Int { return x; } } entity Bar { field g: Foo; } public function main(y: Int): Int { return Bar{Foo{}}.g.f(y); }', [['1i', '1i']], []); 
    });

    it("should exec postfix chains w/ ref", function () {
        runTestSet('entity Foo { method f(inout x: Int): Int { x = x + 1i; return x; } } entity Bar { field g: Foo; } public function main(k: Int): Int { var y: Int = k; let vv = Bar{Foo{}}.g.f(inout y); assert(y == k + 1i); return vv + y; }', [['1i', '4i']], []); 
    });
});
