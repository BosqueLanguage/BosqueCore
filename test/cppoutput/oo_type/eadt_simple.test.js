"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- eADT simple", () => {
    it("should exec simple eADT", function () {
        runMainCode("datatype Foo of F1 { field f: Int; } | F2 { }; public function main(): Int { return F1{3i}.f; }", "3_i"); 
//        runMainCode("datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; public function main(): Bool { return F2{false}.g; }", "false"); 
        runMainCode("datatype Foo<T> of F1 { field f: T; } | F2 { }; public function main(): Int { return F1<Int>{3i}.f; }", "3_i"); 
    });

    it("should exec invariant fail simple eADT", function () {
//        runMainCodeError("datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; public function main(): Int { return F1{-1i}.f; }", "Error -- failed invariant @ test.bsq:3"); 
    });

    it("should exec eADT const", function () {
        runMainCode('datatype Foo of F1 { field f: Int; } | F2 { } & { const c: Int = 3i; } public function main(): Int { return F1::c; }', "3_i"); 
        runMainCode('datatype Foo of F1 { field f: Int; } | F2 { } & { const c: Int = 3i; } public function main(): Int { return Foo::c; }', "3_i"); 
    });

    it("should exec eADT function", function () {
        runMainCode('datatype Foo of F1 { field f: Int; } | F2 { } & { function foo(): Int { return 3i; } } public function main(): Int { return F1::foo(); }', "3_i"); 
        runMainCode('datatype Foo of F1 { field f: Int; } | F2 { } & { function foo(): Int { return 3i; } } public function main(): Int { return Foo::foo(); }', "3_i"); 
    });
});
