"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Int operation trees", () => {
    it("should emit simple pm", function () {
        checkTestEmitMainFunction("public function main(): Int { return 0i + 1i - 4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, 1_i, "test.bsq", 2); Int ᐸtmp_0ᐳ = 0_i + 1_i; ᐸRuntimeᐳ::XInt::checkOverflowSubtraction(ᐸtmp_0ᐳ, 4_i, "test.bsq", 2); return ᐸtmp_0ᐳ - 4_i; }');
        checkTestEmitMainFunction("public function main(): Nat { return (+2n + 2n) - 2n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowAddition(2_n, 2_n, "test.bsq", 2); Nat ᐸtmp_0ᐳ = 2_n + 2_n; ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(ᐸtmp_0ᐳ, 2_n, "test.bsq", 2); return ᐸtmp_0ᐳ - 2_n; }');
    });

    it("should emit precedence pm", function () {
        checkTestEmitMainFunction("public function main(): Int { return 0i + 1i * -4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(1_i, -4_i, "test.bsq", 2); Int ᐸtmp_0ᐳ = 1_i * -4_i; ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, ᐸtmp_0ᐳ, "test.bsq", 2); return 0_i + ᐸtmp_0ᐳ; }');
        checkTestEmitMainFunction("public function main(): Int { return (0i + 1i) * -4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, 1_i, "test.bsq", 2); Int ᐸtmp_0ᐳ = 0_i + 1_i; ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(ᐸtmp_0ᐳ, -4_i, "test.bsq", 2); return ᐸtmp_0ᐳ * -4_i; }');
        checkTestEmitMainFunction("public function main(): Int { return 0i + (1i * -4i); }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(1_i, -4_i, "test.bsq", 2); Int ᐸtmp_0ᐳ = 1_i * -4_i; ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, ᐸtmp_0ᐳ, "test.bsq", 2); return 0_i + ᐸtmp_0ᐳ; }');
        checkTestEmitMainFunction("public function main(): Nat { return +2n // 2n - 2n; }", 'Nat Mainᕒmain() { Nat ᐸtmp_0ᐳ = 2_n / 2_n; ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(ᐸtmp_0ᐳ, 2_n, "test.bsq", 2); return ᐸtmp_0ᐳ - 2_n; }');
        checkTestEmitMainFunction("public function main(): Nat { return (+2n // 2n) - 2n; }", 'Nat Mainᕒmain() { Nat ᐸtmp_0ᐳ = 2_n / 2_n; ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(ᐸtmp_0ᐳ, 2_n, "test.bsq", 2); return ᐸtmp_0ᐳ - 2_n; }');
        checkTestEmitMainFunction("public function main(): Nat { return +2n // (2n - 2n); }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(2_n, 2_n, "test.bsq", 2); Nat ᐸtmp_0ᐳ = 2_n - 2_n; ᐸRuntimeᐳ::XNat::checkDivisionByZero(ᐸtmp_0ᐳ, "test.bsq", 2); return 2_n / ᐸtmp_0ᐳ; }');
    });
});
