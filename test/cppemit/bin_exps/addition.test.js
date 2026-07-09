"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Simple addition", () => {
    it("should emit simple ops", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 0n + 1n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowAddition(0_n, 1_n, "test.bsq", 2); return 0_n + 1_n; }');
        checkTestEmitMainFunction("public function main(): Int { return +2i + -2i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowAddition(2_i, -2_i, "test.bsq", 2); return 2_i + -2_i; }');
    });

    it("should emit chk ops", function () {
        checkTestEmitMainFunction("public function main(): ChkNat { return 0N + 1N; }", 'ChkNat Mainᕒmain() { return 0_N + 1_N; }');
        checkTestEmitMainFunction("public function main(): ChkInt { return +2I + -2I; }", 'ChkInt Mainᕒmain() { return 2_I + -2_I; }');
    });

    it("should emit type alias ops", function () {
        checkTestEmitMainFunction("type Foo = Nat; public function main(x: Foo): Foo { return x + 2n<Foo>; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Nat tmp_0 = x.value; Nat tmp_1 = MainᕒFoo{2_n}.value; ᐸRuntimeᐳ::XNat::checkOverflowAddition(tmp_0, tmp_1, "test.bsq", 2); return MainᕒFoo{tmp_0 + tmp_1}; }');
        checkTestEmitMainFunction("type Foo = Int; public function main(x: Foo): Foo { return 1i<Foo> + x; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Int tmp_0 = MainᕒFoo{1_i}.value; Int tmp_1 = x.value; ᐸRuntimeᐳ::XInt::checkOverflowAddition(tmp_0, tmp_1, "test.bsq", 2); return MainᕒFoo{tmp_0 + tmp_1}; }');

        checkTestEmitMainFunction("type Foo = Nat & { invariant $value != 0n; } public function main(x: Foo): Foo { return x + 2n<Foo>; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(2_n)), "test.bsq", 2, nullptr, "Failed Invariant"); Nat tmp_0 = x.value; Nat tmp_1 = MainᕒFoo{2_n}.value; ᐸRuntimeᐳ::XNat::checkOverflowAddition(tmp_0, tmp_1, "test.bsq", 2); Nat tmp_2 = tmp_0 + tmp_1; ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(tmp_2)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{tmp_2}; }');
        checkTestEmitMainFunction("type Foo = Int & { invariant $value != 0i; } public function main(x: Foo): Foo { return x + x; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Int tmp_0 = x.value; Int tmp_1 = x.value; ᐸRuntimeᐳ::XInt::checkOverflowAddition(tmp_0, tmp_1, "test.bsq", 2); Int tmp_2 = tmp_0 + tmp_1; ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(tmp_2)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{tmp_2}; }');
    });
});
