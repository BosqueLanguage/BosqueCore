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
        checkTestEmitMainFunction("type Foo = Nat; public function main(x: Foo): Foo { return x + 2n<Foo>; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::XNat::checkOverflowAddition(x.value, MainᕒFoo(2_n).value, "test.bsq", 2); return MainᕒFoo((x.value) + (MainᕒFoo(2_n).value)); }');
        checkTestEmitMainFunction("type Foo = Int; public function main(x: Foo): Foo { return 1i<Foo> + x; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::XInt::checkOverflowAddition(MainᕒFoo(1_i).value, x.value, "test.bsq", 2); return MainᕒFoo((MainᕒFoo(1_i).value) + (x.value)); }');

        checkTestEmitMainFunction("type Foo = Nat & { invariant $value != 0n; } public function main(x: Foo): Foo { return x + 2n<Foo>; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(2_n)), "test.bsq", 2, nullptr, "Failed Invariant"); ᐸRuntimeᐳ::XNat::checkOverflowAddition(x.value, MainᕒFoo(2_n).value, "test.bsq", 2); ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0((x.value) + (MainᕒFoo(2_n).value))), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo((x.value) + (MainᕒFoo(2_n).value)); }');
        checkTestEmitMainFunction("type Foo = Int & { invariant $value != 0i; } public function main(x: Foo): Foo { return x + x; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::XInt::checkOverflowAddition(x.value, x.value, "test.bsq", 2); ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0((x.value) + (x.value))), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo((x.value) + (x.value)); }');
    });
});
