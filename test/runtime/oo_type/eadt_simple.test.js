"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- eADT simple", () => {
    it("should exec simple eADT", function () {
        runMainCode("datatype Foo of F1 { field f: Int; } | F2 { }; public function main(): Int { return F1{3i}.f; }", [3n, "Int"]); 
        runMainCode("datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; public function main(): Bool { return F2{false}.g; }", [false, "Bool"]); 
        runMainCode("datatype Foo<T> of F1 { field f: T; } | F2 { }; public function main(): Int { return F1<Int>{3i}.f; }", [3n, "Int"]); 
    });

    it("should exec invariant fail simple eADT", function () {
        runMainCodeError("datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; public function main(): Int { return F1{-1i}.f; }", "Error -- failed invariant @ test.bsq:3"); 
    });
});
