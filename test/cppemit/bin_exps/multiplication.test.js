"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Simple multiplication", () => {
    it("should emit simple ops", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 1n * 1n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowMultiplication(1_n, 1_n, "test.bsq", 2); return 1_n * 1_n; }');
        checkTestEmitMainFunction("public function main(): Int { return 2i * -2i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(2_i, -2_i, "test.bsq", 2); return 2_i * -2_i; }');
    });


    it("should emit type alias ops", function () {
        checkTestEmitMainFunction("type Foo = Nat; public function main(x: Foo): Foo { return x * 2n; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::XNat::checkOverflowMultiplication(x.value, 2_n, "test.bsq", 2); return MainᕒFoo{(x.value) * 2_n}; }');
        checkTestEmitMainFunction("type Foo = Int; public function main(x: Foo): Foo { return 1i * x; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(1_i, x.value, "test.bsq", 2); return MainᕒFoo{1_i * (x.value)}; }');

        checkTestEmitMainFunction("type Foo = Nat & { invariant $value != 0n; } public function main(x: Foo): Foo { return x * 2n; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::XNat::checkOverflowMultiplication(x.value, 2_n, "test.bsq", 2); ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0((x.value) * 2_n)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{(x.value) * 2_n}; }');
    });
});
