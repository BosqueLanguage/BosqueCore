"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Simple subtraction", () => {
    it("should emit simple ops", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 1n - 1n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(1_n, 1_n, "test.bsq", 2); return 1_n - 1_n; }');
        checkTestEmitMainFunction("public function main(): Int { return 2i - -2i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowSubtraction(2_i, -2_i, "test.bsq", 2); return 2_i - -2_i; }');
    });

    it("should fail underflow", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 1n - 5n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(1_n, 5_n, "test.bsq", 2); return 1_n - 5_n; }');
    });

    it("should emit type alias ops", function () {
        checkTestEmitMainFunction("type Foo = Nat; public function main(x: Foo): Foo { return x - 2n<Foo>; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Nat ᐸtmp_0ᐳ = x.value; Nat ᐸtmp_1ᐳ = MainᕒFoo{2_n}.value; ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(ᐸtmp_0ᐳ, ᐸtmp_1ᐳ, "test.bsq", 2); return MainᕒFoo{ᐸtmp_0ᐳ - ᐸtmp_1ᐳ}; }');
        checkTestEmitMainFunction("type Foo = Int; public function main(x: Foo): Foo { return 1i<Foo> - x; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Int ᐸtmp_0ᐳ = MainᕒFoo{1_i}.value; Int ᐸtmp_1ᐳ = x.value; ᐸRuntimeᐳ::XInt::checkOverflowSubtraction(ᐸtmp_0ᐳ, ᐸtmp_1ᐳ, "test.bsq", 2); return MainᕒFoo{ᐸtmp_0ᐳ - ᐸtmp_1ᐳ}; }');

        checkTestEmitMainFunction("type Foo = Nat & { invariant $value != 0n; } public function main(x: Foo): Foo { return x - 2n<Foo>; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(2_n)), "test.bsq", 2, nullptr, "Failed Invariant"); Nat ᐸtmp_0ᐳ = x.value; Nat ᐸtmp_1ᐳ = MainᕒFoo{2_n}.value; ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(ᐸtmp_0ᐳ, ᐸtmp_1ᐳ, "test.bsq", 2); Nat ᐸtmp_2ᐳ = ᐸtmp_0ᐳ - ᐸtmp_1ᐳ; ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(ᐸtmp_2ᐳ)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{ᐸtmp_2ᐳ}; }');
        checkTestEmitMainFunction("type Foo = Int & { invariant $value != 0i; } public function main(x: Foo): Foo { return x - x; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { Int ᐸtmp_0ᐳ = x.value; Int ᐸtmp_1ᐳ = x.value; ᐸRuntimeᐳ::XInt::checkOverflowSubtraction(ᐸtmp_0ᐳ, ᐸtmp_1ᐳ, "test.bsq", 2); Int ᐸtmp_2ᐳ = ᐸtmp_0ᐳ - ᐸtmp_1ᐳ; ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(ᐸtmp_2ᐳ)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{ᐸtmp_2ᐳ}; }');
    });
});
