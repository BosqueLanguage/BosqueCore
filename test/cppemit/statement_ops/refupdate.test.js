"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- ref updates", () => {
    it("should emit ref updates direct", function () {
        checkTestEmitMainFunction('entity Foo { field x: Int; } public function main(x: Int): Int { var z = Foo{x}; ref z[x = 5i]; return z.x; }', 'Int Mainᕒmain(Int x) { MainᕒFoo z = MainᕒFoo{x}; { Int ᑯx = z.x; z = {5_i}; } return z.x; }');
        
        checkTestEmitMainFunction('entity Foo { field x: Int; } public function main(x: Int): Int { ref z = Foo{x}; ref z[x = $x + 1i]; return z.x; }', 'Int Mainᕒmain(Int x) { MainᕒFoo z = MainᕒFoo{x}; { Int ᑯx = z.x; ᐸRuntimeᐳ::XInt::checkOverflowAddition(ᑯx, 1_i, "test.bsq", 2); z = {ᑯx + 1_i}; } return z.x; }');

        checkTestEmitMainFunction('entity Foo { field x: Int; field y: Bool; } public function main(x: Int): Int { ref z = Foo{x, false}; ref z[x = 5i]; return z.x; }', 'Int Mainᕒmain(Int x) { MainᕒFoo z = MainᕒFoo{x, FALSE}; { Int ᑯx = z.x; z = {5_i, z.y}; } return z.x; }');
        checkTestEmitMainFunction('entity Foo { field x: Int; field y: Bool; } public function main(x: Int): Int { ref z = Foo{x, false}; ref z[y = true, x = 9i]; return z.x; }', 'Int Mainᕒmain(Int x) { MainᕒFoo z = MainᕒFoo{x, FALSE}; { Int ᑯx = z.x; Bool ᑯy = z.y; z = {9_i, TRUE}; } return z.x; }');
    });

    it("should emit ref updates direct with inherits/template", function () {
        checkTestEmitMainFunction('concept Bar { field g: Bool; } entity Foo provides Bar { field x: Int; } public function main(x: Int): Int { var z = Foo{true, x}; ref z[x = 5i]; return z.x; }', 'Int Mainᕒmain(Int x) { MainᕒFoo z = MainᕒFoo{TRUE, x}; { Int ᑯx = z.x; z = {z.g, 5_i}; } return z.x; }');
        checkTestEmitMainFunction('concept Bar { field g: Bool; } entity Foo provides Bar { field x: Int; } public function main(x: Int): Bool { var z = Foo{true, x}; ref z[g = false]; return z.g; }', 'Bool Mainᕒmain(Int x) { MainᕒFoo z = MainᕒFoo{TRUE, x}; { Bool ᑯg = z.g; z = {FALSE, z.x}; } return z.g; }');

        checkTestEmitMainFunction('entity Foo<T> { field x: T; } public function main(x: Int): Int { var z = Foo<Int>{x}; ref z[x = 5i]; return z.x; }', 'Int Mainᕒmain(Int x) { MainᕒFooᐸIntᐳ z = MainᕒFooᐸIntᐳ{x}; { Int ᑯx = z.x; z = {5_i}; } return z.x; }');

        checkTestEmitMainFunction('concept Bar<T> { field g: T; } entity Foo<T> provides Bar<T> { field x: Int; } public function main(x: Int): Int { var z = Foo<Bool>{true, x}; ref z[x = 5i]; return z.x; }', 'Int Mainᕒmain(Int x) { MainᕒFooᐸBoolᐳ z = MainᕒFooᐸBoolᐳ{TRUE, x}; { Int ᑯx = z.x; z = {z.g, 5_i}; } return z.x; }');
        checkTestEmitMainFunction('concept Bar<T> { field g: T; } entity Foo<T> provides Bar<T> { field x: Int; } public function main(x: Int): Bool { var z = Foo<Bool>{true, x}; ref z[g = z.x == 0i]; return z.g; }', 'Bool Mainᕒmain(Int x) { MainᕒFooᐸBoolᐳ z = MainᕒFooᐸBoolᐳ{TRUE, x}; { Bool ᑯg = z.g; z = {z.x == 0_i, z.x}; } return z.g; }');
    });

    it("should emit ref updates direct with invariants", function () {
        checkTestEmitMainFunction('entity Foo { field x: Int; invariant $x < 5i; } public function main(x: Int): Int { ref z = Foo{x}; ref z[x = $x + 1i]; return z.x; }', 'Int Mainᕒmain(Int x) { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(x)), "test.bsq", 2, nullptr, "Failed Invariant"); MainᕒFoo z = MainᕒFoo{x}; { Int ᑯx = z.x; ᐸRuntimeᐳ::XInt::checkOverflowAddition(ᑯx, 1_i, "test.bsq", 2); Int tmp_0 = ᑯx + 1_i; ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(tmp_0)), "test.bsq", 2, nullptr, "Failed Invariant"); z = {tmp_0}; } return z.x; }');
        checkTestEmitMainFunction('concept Bar { field g: Bool; invariant $g; } entity Foo provides Bar { field x: Int; } public function main(x: Int): Bool { var z = Foo{true, x}; ref z[g = z.x != 0i]; return z.g; }', 'Bool Mainᕒmain(Int x) { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒBarᐤinvariant_0(TRUE)), "test.bsq", 2, nullptr, "Failed Invariant"); MainᕒFoo z = MainᕒFoo{TRUE, x}; { Bool ᑯg = z.g; Bool tmp_0 = z.x != 0_i; Int tmp_1 = z.x; ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒBarᐤinvariant_0(tmp_0, tmp_1)), "test.bsq", 2, nullptr, "Failed Invariant"); z = {tmp_0, tmp_1}; } return z.g; }');
    });

    it("should emit ref updates as params", function () {
        checkTestEmitMainFunction('entity Foo { field x: Int; } function f(ref z: Foo): Int { ref z[x = 5i]; return z.x; } public function main(): Int { ref z = Foo{3i}; return f(ref z); }', 'Int Mainᕒmain() { MainᕒFoo z = MainᕒFoo{3_i}; Int tmp_0 = Mainᕒfᙾref(z); return tmp_0; }');
        checkTestEmitMainFunction('entity Foo { field x: Int; ref method f() { ref this[x = 0i]; return; } } public function main(): Int { ref z = Foo{3i}; ref z.f(); return z.x; }', 'Int Mainᕒmain() { MainᕒFoo z = MainᕒFoo{3_i}; MainᕒFooᑀfᙾref(z); return z.x; }');

        //don't need return value for Void invokes
        checkTestEmitMainFunction('entity Foo { field x: Int; ref method f() { ref this[x = 0i]; } } public function main(): Int { ref z = Foo{3i}; ref z.f(); return z.x; }', 'Int Mainᕒmain() { MainᕒFoo z = MainᕒFoo{3_i}; MainᕒFooᑀfᙾref(z); return z.x; }');
    });
});
