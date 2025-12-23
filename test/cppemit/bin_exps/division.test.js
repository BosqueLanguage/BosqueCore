"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";


describe ("CPPEmit -- Simple division", () => {
    it("should emit simple nats", function () {
        checkTestEmitMainFunction("public function main(x: Nat): Nat { return 1n // x; }", 'Nat Mainᕒmain(Nat x) { ᐸRuntimeᐳ::XNat::checkDivisionByZero(1_n, "test.bsq", 2); return 1_n / x; }');
        checkTestEmitMainFunction("public function main(x: Int): Int { return +2i // x; }", 'Int Mainᕒmain(Int x) { ᐸRuntimeᐳ::XInt::checkDivisionByZero(2_i, "test.bsq", 2); return 2_i / x; }');
    });

    it("should emit simple nats -- elim test for const", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 1n // 1n; }", 'Nat Mainᕒmain() { return 1_n / 1_n; }');
        checkTestEmitMainFunction("public function main(): Int { return +2i // -2i; }", 'Int Mainᕒmain() { return 2_i / -2_i; }');
    });

    it("should fail div 0", function () {
        checkTestEmitMainFunction("public function main(): Int { return 2i // 0i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkDivisionByZero(2_i, "test.bsq", 2); return 2_i / 0_i; }');
    });
});
