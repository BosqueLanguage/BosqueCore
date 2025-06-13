"use strict";

import { runishMainCodeUnsat, runishMainCodeSat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- entity simple field access", () => {
    it("should SMT exec simple entity", function () {
        runishMainCodeUnsat("entity Foo { field x: Int; field y: Int; } public function main(v: Foo): Int { return v.x; }", "(declare-const b Int) (assert (= b (Main@main (Main@Foo-mk 3 5)))) (assert (not (= b 3)))"); 
        runishMainCodeUnsat("entity Foo { field x: Int; field y: Int; } public function main(v: Foo): Int { return v.x + v.y; }", "(declare-const b Int) (assert (= b (Main@main (Main@Foo-mk 3 5)))) (assert (not (= b 8)))"); 

        runishMainCodeUnsat("entity Foo { field x: Int; field y: Int; } public function main(v: Foo): Int { let k = v.x + 1i; assert k > v.x; return k; }", "(declare-const b (@Result Int)) (assert (= b (Main@main (Main@Foo-mk 3 5)))) (assert (not (= b (@Result-ok 4))))"); 
    });

    it("should SMT found error simple entity", function () {
        runishMainCodeSat("entity Foo { field x: Int; field y: Int; } public function main(v: Foo): Int { let k = v.x + v.y; assert k != v.x; return k; }", "(declare-const f Main@Foo) (declare-const res (@Result Int)) (assert (= res (Main@main f))) (assert (= res @Result-err-other))"); 
    });

    it("should exec invariant fail simple entity", function () {
        runishMainCodeUnsat("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Int { return Foo{3i}.f; }", "(assert (not (= (@Result-ok 3) Main@main)))"); 
        runishMainCodeUnsat("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Int { return Foo{-1i}.f; }", "(assert (not (= (as @Result-err-other (@Result Int)) Main@main)))"); 
    });
});


