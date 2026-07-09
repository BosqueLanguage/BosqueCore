"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- type decl of bool", () => {
    it("should emit bool type decl", function () {
        checkTestEmitMainFunction("type Flag = Bool; public function main(): Flag { let e = true<Flag>; return e; }", 'MainᕒFlag Mainᕒmain() { MainᕒFlag e = MainᕒFlag{TRUE}; return e; }');
    });
});

describe ("CPPEmit -- type decl of number", () => {
    it("should emit numeric type decls", function () {
        checkTestEmitMainFunction('type NVal = Int; public function main(): NVal { let e = -2i<NVal>; return e; }', 'MainᕒNVal Mainᕒmain() { MainᕒNVal e = MainᕒNVal{-2_i}; return e; }');
    });
});

describe ("CPPEmit -- type decl of number with numeric range", () => {
    it("should emit Int range check", function () {
        checkTestEmitMainFunction('type Foo = Int{1i, 10i}; public function main(): Foo { let e = Foo{5i}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(5_i >= 1_i), "test.bsq", 2, nullptr, "Value below range minimum 1i"); ᐸRuntimeᐳ::bsq_invariant((bool)(5_i <= 10_i), "test.bsq", 2, nullptr, "Value above range maximum 10i"); MainᕒFoo e = MainᕒFoo{5_i}; return e; }');
    });

    it("should emit Nat range check", function () {
        checkTestEmitMainFunction('type Foo = Nat{0n, 100n}; public function main(): Foo { let e = Foo{50n}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(50_n >= 0_n), "test.bsq", 2, nullptr, "Value below range minimum 0n"); ᐸRuntimeᐳ::bsq_invariant((bool)(50_n <= 100_n), "test.bsq", 2, nullptr, "Value above range maximum 100n"); MainᕒFoo e = MainᕒFoo{50_n}; return e; }');
    });

    it("should emit Float range check", function () {
        checkTestEmitMainFunction('type Foo = Float{0.0f, 1.0f}; public function main(): Foo { let e = Foo{0.5f}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(0.5_f >= 0.0_f), "test.bsq", 2, nullptr, "Value below range minimum 0.0f"); ᐸRuntimeᐳ::bsq_invariant((bool)(0.5_f <= 1.0_f), "test.bsq", 2, nullptr, "Value above range maximum 1.0f"); MainᕒFoo e = MainᕒFoo{0.5_f}; return e; }');
    });

    it("should emit single-value exact range check", function () {
        checkTestEmitMainFunction('type Foo = Int{5i}; public function main(): Foo { let e = Foo{5i}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(5_i >= 5_i), "test.bsq", 2, nullptr, "Value below range minimum 5i"); ᐸRuntimeᐳ::bsq_invariant((bool)(5_i <= 5_i), "test.bsq", 2, nullptr, "Value above range maximum 5i"); MainᕒFoo e = MainᕒFoo{5_i}; return e; }');
    });

    it("should emit min-only range check", function () {
        checkTestEmitMainFunction('type Foo = Int{5i, }; public function main(): Foo { let e = Foo{10i}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(10_i >= 5_i), "test.bsq", 2, nullptr, "Value below range minimum 5i"); MainᕒFoo e = MainᕒFoo{10_i}; return e; }');
    });

    it("should emit max-only range check", function () {
        checkTestEmitMainFunction('type Foo = Int{, 10i}; public function main(): Foo { let e = Foo{5i}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(5_i <= 10_i), "test.bsq", 2, nullptr, "Value above range maximum 10i"); MainᕒFoo e = MainᕒFoo{5_i}; return e; }');
    });

    it("should emit ChkInt range check", function () {
        checkTestEmitMainFunction('type Foo = ChkInt{1I, 10I}; public function main(): Foo { let e = Foo{5I}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(5_I >= 1_I), "test.bsq", 2, nullptr, "Value below range minimum 1I"); ᐸRuntimeᐳ::bsq_invariant((bool)(5_I <= 10_I), "test.bsq", 2, nullptr, "Value above range maximum 10I"); MainᕒFoo e = MainᕒFoo{5_I}; return e; }');
    });

    it("should emit ChkNat range check", function () {
        checkTestEmitMainFunction('type Foo = ChkNat{0N, 100N}; public function main(): Foo { let e = Foo{50N}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(50_N >= 0_N), "test.bsq", 2, nullptr, "Value below range minimum 0N"); ᐸRuntimeᐳ::bsq_invariant((bool)(50_N <= 100_N), "test.bsq", 2, nullptr, "Value above range maximum 100N"); MainᕒFoo e = MainᕒFoo{50_N}; return e; }');
    });
});

describe ("CPPEmit -- type decl of number with invariants", () => {
    it("should emit positional", function () {
        checkTestEmitMainFunction('type Foo = Int & { invariant $value > 3i; } public function main(): Foo { let e = Foo{5i}; return e; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(5_i)), "test.bsq", 2, nullptr, "Failed Invariant"); MainᕒFoo e = MainᕒFoo{5_i}; return e; }');
    });
});

describe ("CPPEmit -- numeric range check on arithmetic", () => {
    it("should emit range check on addition result", function () {
        checkTestEmitMainFunction('type Foo = Int{1i, 10i}; public function main(x: Foo, y: Foo): Foo { return x + y; }', 'MainᕒFoo Mainᕒmain(MainᕒFoo x, MainᕒFoo y) { Int tmp_0 = x.value; Int tmp_1 = y.value; ᐸRuntimeᐳ::XInt::checkOverflowAddition(tmp_0, tmp_1, "test.bsq", 2); Int tmp_2 = tmp_0 + tmp_1; ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_2 >= 1_i), "test.bsq", 2, nullptr, "Value below range minimum 1i"); ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_2 <= 10_i), "test.bsq", 2, nullptr, "Value above range maximum 10i"); return MainᕒFoo{tmp_2}; }');
    });

    it("should emit range check on subtraction result", function () {
        checkTestEmitMainFunction('type Foo = Int{1i, 10i}; public function main(x: Foo, y: Foo): Foo { return x - y; }', 'MainᕒFoo Mainᕒmain(MainᕒFoo x, MainᕒFoo y) { Int tmp_0 = x.value; Int tmp_1 = y.value; ᐸRuntimeᐳ::XInt::checkOverflowSubtraction(tmp_0, tmp_1, "test.bsq", 2); Int tmp_2 = tmp_0 - tmp_1; ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_2 >= 1_i), "test.bsq", 2, nullptr, "Value below range minimum 1i"); ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_2 <= 10_i), "test.bsq", 2, nullptr, "Value above range maximum 10i"); return MainᕒFoo{tmp_2}; }');
    });

    it("should emit range check on multiplication result", function () {
        checkTestEmitMainFunction('type Foo = Int{1i, 10i}; public function main(x: Foo): Foo { return x * 2i; }', 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Int tmp_0 = x.value; ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(tmp_0, 2_i, "test.bsq", 2); Int tmp_1 = tmp_0 * 2_i; ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_1 >= 1_i), "test.bsq", 2, nullptr, "Value below range minimum 1i"); ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_1 <= 10_i), "test.bsq", 2, nullptr, "Value above range maximum 10i"); return MainᕒFoo{tmp_1}; }');
    });

    it("should emit range check on division result", function () {
        checkTestEmitMainFunction('type Foo = Int{1i, 10i}; public function main(x: Foo): Foo { return x // 2i; }', 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Int tmp_0 = (x.value) / 2_i; ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_0 >= 1_i), "test.bsq", 2, nullptr, "Value below range minimum 1i"); ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_0 <= 10_i), "test.bsq", 2, nullptr, "Value above range maximum 10i"); return MainᕒFoo{tmp_0}; }');
    });

    it("should emit range check on negation result", function () {
        checkTestEmitMainFunction('type Foo = Int{-10i, 10i}; public function main(x: Foo): Foo { return -x; }', 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Int tmp_0 = -(x.value); ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_0 >= -10_i), "test.bsq", 2, nullptr, "Value below range minimum -10i"); ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_0 <= 10_i), "test.bsq", 2, nullptr, "Value above range maximum 10i"); return MainᕒFoo{tmp_0}; }');
    });

    it("should emit both invariant and range check on addition result", function () {
        checkTestEmitMainFunction('type Foo = Int{1i, 100i} & { invariant $value != 7i; } public function main(x: Foo, y: Foo): Foo { return x + y; }', 'MainᕒFoo Mainᕒmain(MainᕒFoo x, MainᕒFoo y) { Int tmp_0 = x.value; Int tmp_1 = y.value; ᐸRuntimeᐳ::XInt::checkOverflowAddition(tmp_0, tmp_1, "test.bsq", 2); Int tmp_2 = tmp_0 + tmp_1; ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(tmp_2)), "test.bsq", 2, nullptr, "Failed Invariant"); ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_2 >= 1_i), "test.bsq", 2, nullptr, "Value below range minimum 1i"); ᐸRuntimeᐳ::bsq_invariant((bool)(tmp_2 <= 100_i), "test.bsq", 2, nullptr, "Value above range maximum 100i"); return MainᕒFoo{tmp_2}; }');
    });
});
