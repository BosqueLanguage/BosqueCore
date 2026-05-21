"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- elist decl and access", () => {
    it("should exec simple elist", function () {
        runTestSet('public function main(z: Int): (|Int, Bool|) { return (|z, true|); }', [['0i', '(| 0i, true |)']], []); 
        runTestSet('public function main(x: (|Int, Bool|)): Int { return 1i + x.0; }', [['(| 0i, true |)', '1i']], []); 
    });

    it("should exec nesting", function () {
        runTestSet('public function main(v: (|Int, (|Bool, Bool|)|)): Bool { return v.1.0; }', [['(| 0i, (|false, true|)|)', 'false']], []); 
        runTestSet('entity Foo { field pp: (|Int, Bool|); } public function main(v: Int): Foo { return Foo{(|v, false|)}; }', [['5i', 'Main::Foo{ (| 5i, false |) }']], []); 
    
        runTestSet('public function main(v: Int): Int { let x: Option<(|Int, Bool|)> = some((|v, true|)); return x.@some.0; }', [['3i', '3i']], []); 
    });
});
