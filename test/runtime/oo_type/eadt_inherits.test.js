"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- entity decl inherits", () => {
    it("should exec simple inherits eADT", function () {
        runMainCode('datatype Foo using { field f: Int; } of | F1 { } | F2 { }; public function main(): Int { return F1{3i}.f; }', "3i"); 
        runMainCode('datatype Foo using { field f: Int; invariant $f >= 0i; } of | F1 { } | F2 { field g: Bool; }; public function main(): Bool { return F2{3i, false}.g; }', "false"); 

        runMainCode('datatype Foo<T> using { field f: T; } of | F1 { } | F2 { }; public function main(): Int { return F1<Int>{3i}.f; }', "3i"); 

        runMainCode('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of | F1 { invariant $g ==> $f >= 0i; } | F2 { }; public function main(): Int { return F1{3i, true}.f; }', "3i"); 
        runMainCode('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of | F1 { invariant $g ==> $f >= 0i; } | F2 { }; public function main(): Int { return F1{-1i, false}.f; }', "-1i"); 
    });

    it("should fail exec simple inherits eADT", function () {
        runMainCodeError('concept Bar<U> { field f: U; } datatype Foo provides Bar<Int> using { field g: Bool; } of | F1 { invariant $g ==> $f >= 0i; } | F2 { }; public function main(): Int { return F1{-1i, true}.f; }', "Error -- failed invariant @ test.bsq:3"); 
    });
});
