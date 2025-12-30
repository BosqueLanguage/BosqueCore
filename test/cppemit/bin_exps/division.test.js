"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";


describe ("CPPEmit -- Simple division", () => {
    it("should emit simple nats", function () {
        checkTestEmitMainFunction("public function main(x: Nat): Nat { return 1n // x; }", 'Nat Mainᕒmain(Nat x) { ᐸRuntimeᐳ::XNat::checkDivisionByZero(x, "test.bsq", 2); return 1_n / x; }');
        checkTestEmitMainFunction("public function main(x: Int): Int { return +2i // x; }", 'Int Mainᕒmain(Int x) { ᐸRuntimeᐳ::XInt::checkDivisionByZero(x, "test.bsq", 2); return 2_i / x; }');
    });

    it("should emit simple nats -- elim test for const", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 1n // 1n; }", 'Nat Mainᕒmain() { return 1_n / 1_n; }');
        checkTestEmitMainFunction("public function main(): Int { return +2i // -2i; }", 'Int Mainᕒmain() { return 2_i / -2_i; }');
    });

    it("should fail div 0", function () {
        checkTestEmitMainFunction("public function main(): Int { return 2i // 0i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkDivisionByZero(0_i, "test.bsq", 2); return 2_i / 0_i; }');
    });

    it("should emit type alias ops", function () {
        checkTestEmitMainFunction("type Foo = Nat; public function main(x: Foo): Foo { return x // 2n; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { return MainᕒFoo((x.value) / 2_n); }');
        checkTestEmitMainFunction("type Foo = Int; public function main(x: Foo): Int { return 1i<Foo> // x; }", 'Int Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::XInt::checkDivisionByZero(x.value, "test.bsq", 2); return (MainᕒFoo(1_i).value) / (x.value); }');

        checkTestEmitMainFunction("type Foo = Nat & { invariant $value != 0n; } public function main(x: Foo): Foo { return x // 2n; }", 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0((x.value) / 2_n)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo((x.value) / 2_n); }');
    });
});
