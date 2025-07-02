"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";
/*
describe ("SMT -- eADT simple", () => {
    it("should smt exec simple eADT", function () {
        runMainCode("datatype Foo of F1 { field f: Int; } | F2 { }; public function main(): Int { return F1{3i}.f; }", "3i"); 
        runMainCode("datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; public function main(): Bool { return F2{false}.g; }", "false"); 
        runMainCode("datatype Foo<T> of F1 { field f: T; } | F2 { }; public function main(): Int { return F1<Int>{3i}.f; }", "3i"); 
    });

    it("should smt exec invariant fail simple eADT", function () {
        runMainCodeError("datatype Foo of F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; public function main(): Int { return F1{-1i}.f; }", "Error -- failed invariant @ test.bsq:3"); 
    });

    it("should smt exec eADT const", function () {
        runMainCode('datatype Foo of F1 { field f: Int; } | F2 { } & { const c: Int = 3i; } public function main(): Int { return F1::c; }', "3i"); 
        runMainCode('datatype Foo of F1 { field f: Int; } | F2 { } & { const c: Int = 3i; } public function main(): Int { return Foo::c; }', "3i"); 
    });

    it("should smt exec eADT function", function () {
        runMainCode('datatype Foo of F1 { field f: Int; } | F2 { } & { function foo(): Int { return 3i; } } public function main(): Int { return F1::foo(); }', "3i"); 
        runMainCode('datatype Foo of F1 { field f: Int; } | F2 { } & { function foo(): Int { return 3i; } } public function main(): Int { return Foo::foo(); }', "3i"); 
    });
});
*/