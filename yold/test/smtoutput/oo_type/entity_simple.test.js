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
        runishMainCodeSat("entity Foo { field x: Int; field y: Int; } public function main(v: Foo): Int { let k = v.x + v.y; assert k != v.x; return k; }", "(declare-const f Main@Foo) (declare-const res (@Result Int)) (assert (= res (Main@main f))) (assert (is-@Result-err res))"); 
    });

    it("should exec invariant fail simple entity", function () {
        runishMainCodeUnsat("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Int { return Foo{3i}.f; }", "(assert (not (= (@Result-ok 3) Main@main)))"); 
        runishMainCodeUnsat("entity Foo { field f: Int; invariant $f >= 0i; } public function main(): Int { return Foo{-1i}.f; }", "(assert (not (is-@Result-err Main@main)))"); 
    });
});
/*
describe ("SMT -- entity simple with default fields", () => {
    it("should exec smt simple entity", function () {
        runMainCode("entity Foo { field f: Int = 3i; } public function main(): Int { return Foo{3i}.f; }", "3i"); 

        runMainCode("entity Foo { field f: Int; field g: Int = $f; } public function main(): Int { return Foo{3i, 5i}.g; }", "5i"); 
        runMainCode("entity Foo { field f: Int; field g: Int = $f; } public function main(): Int { return Foo{3i}.g; }", "3i"); 
    });
});
*/
describe ("SMT -- entity decl with consts", () => {
    it("should exec smt entity with consts", function () {
        runishMainCodeUnsat('entity Foo { const c: Int = 3i; } public function main(): Int { return Foo::c; }', "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat('entity Foo<T> { const c: Int = 3i; } public function main(): Int { return Foo<Nat>::c; }', "(assert (not (= 3 Main@main)))"); 
    });
});

describe ("SMT -- entity decl with functions", () => {
    it("should exec smt entity with functions", function () {
        runishMainCodeUnsat('entity Foo { function foo(): Int { return 3i; } } public function main(): Int { return Foo::foo(); }', "(assert (not (= 3 Main@main)))");

        runishMainCodeUnsat('entity Foo<T> { function foo(x: T): T { return x; } } public function main(): Int { return Foo<Int>::foo(3i); }', "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat('entity Foo { function foo<T>(x: T): T { return x; } } public function main(): Int { return Foo::foo<Int>(3i); }', "(assert (not (= 3 Main@main)))");

        runishMainCodeUnsat('entity Foo { function foo(x: Int): Int { assert x != 0i; return x; } } public function main(): Int { return Foo::foo(3i); }', "(assert (not (= (@Result-ok 3) Main@main)))");
    });
});

