"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- eADT simple", () => {
    it("should smt exec simple eADT", function () {
        runishMainCodeUnsat("datatype Foo of | F1 { field f: Int; } | F2 { }; public function main(): Int { return F1{3i}.f; }", "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat("datatype Foo of | F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; public function main(): Bool { return F2{false}.g; }", "(assert Main@main)"); 
        runishMainCodeUnsat("datatype Foo<T> of | F1 { field f: T; } | F2 { }; public function main(): Int { return F1<Int>{3i}.f; }", "(assert (not (= 3 Main@main)))"); 
    });

    it("should smt exec invariant fail simple eADT", function () {
        runishMainCodeUnsat("datatype Foo of | F1 { field f: Int; invariant $f >= 0i; } | F2 { field g: Bool; }; public function main(): Int { return F1{-1i}.f; }", "(assert (not (is-@Result-err Main@main)))"); 
    });

    it("should smt exec eADT const", function () {
        runishMainCodeUnsat('datatype Foo of | F1 { field f: Int; } | F2 { } & { const c: Int = 3i; } public function main(): Int { return F1::c; }', "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat('datatype Foo of | F1 { field f: Int; } | F2 { } & { const c: Int = 3i; } public function main(): Int { return Foo::c; }', "(assert (not (= 3 Main@main)))"); 
    });

    it("should smt exec eADT function", function () {
        runishMainCodeUnsat('datatype Foo of | F1 { field f: Int; } | F2 { } & { function foo(): Int { return 3i; } } public function main(): Int { return F1::foo(); }', "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat('datatype Foo of | F1 { field f: Int; } | F2 { } & { function foo(): Int { return 3i; } } public function main(): Int { return Foo::foo(); }', "(assert (not (= 3 Main@main)))"); 
    });
});
