"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Int operation trees", () => {
    it("should check simple pm", function () {
        checkTestEmitMainFunction("public function main(): Int { return 0i + 1i - 4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, 1_i, "test.bsq", 2); ᐸRuntimeᐳ::XInt::checkOverflowSubtraction(0_i + 1_i, 4_i, "test.bsq", 2); return (0_i + 1_i) - 4_i; }');
        checkTestEmitMainFunction("public function main(): Nat { return (+2n + 2n) - 2n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowAddition(2_n, 2_n, "test.bsq", 2); ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(2_n + 2_n, 2_n, "test.bsq", 2); return (2_n + 2_n) - 2_n; }');
    });

    it("should check precedence pm", function () {
        checkTestEmitMainFunction("public function main(): Int { return 0i + 1i * -4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(1_i, -4_i, "test.bsq", 2); ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, 1_i * -4_i, "test.bsq", 2); return 0_i + (1_i * -4_i); }');
        checkTestEmitMainFunction("public function main(): Int { return (0i + 1i) * -4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, 1_i, "test.bsq", 2); ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(0_i + 1_i, -4_i, "test.bsq", 2); return (0_i + 1_i) * -4_i; }');
        checkTestEmitMainFunction("public function main(): Int { return 0i + (1i * -4i); }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(1_i, -4_i, "test.bsq", 2); ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, 1_i * -4_i, "test.bsq", 2); return 0_i + (1_i * -4_i); }');
        checkTestEmitMainFunction("public function main(): Nat { return +2n // 2n - 2n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(2_n / 2_n, 2_n, "test.bsq", 2); return (2_n / 2_n) - 2_n; }');
        checkTestEmitMainFunction("public function main(): Nat { return (+2n // 2n) - 2n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(2_n / 2_n, 2_n, "test.bsq", 2); return (2_n / 2_n) - 2_n; }');
        checkTestEmitMainFunction("public function main(): Nat { return +2n // (2n - 2n); }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(2_n, 2_n, "test.bsq", 2); ᐸRuntimeᐳ::XNat::checkDivisionByZero(2_n - 2_n, "test.bsq", 2); return 2_n / (2_n - 2_n); }');
    });
});
