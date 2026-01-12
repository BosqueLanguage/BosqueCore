"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Int operation trees", () => {
    it("should emit simple pm", function () {
        checkTestEmitMainFunction("public function main(): Int { return 0i + 1i - 4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, 1_i, "test.bsq", 2); Int tmp_0 = 0_i + 1_i; ᐸRuntimeᐳ::XInt::checkOverflowSubtraction(tmp_0, 4_i, "test.bsq", 2); return tmp_0 - 4_i; }');
        checkTestEmitMainFunction("public function main(): Nat { return (+2n + 2n) - 2n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowAddition(2_n, 2_n, "test.bsq", 2); Nat tmp_0 = 2_n + 2_n; ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(tmp_0, 2_n, "test.bsq", 2); return tmp_0 - 2_n; }');
    });

    it("should emit precedence pm", function () {
        checkTestEmitMainFunction("public function main(): Int { return 0i + 1i * -4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(1_i, -4_i, "test.bsq", 2); Int tmp_0 = 1_i * -4_i; ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, tmp_0, "test.bsq", 2); return 0_i + tmp_0; }');
        checkTestEmitMainFunction("public function main(): Int { return (0i + 1i) * -4i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, 1_i, "test.bsq", 2); Int tmp_0 = 0_i + 1_i; ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(tmp_0, -4_i, "test.bsq", 2); return tmp_0 * -4_i; }');
        checkTestEmitMainFunction("public function main(): Int { return 0i + (1i * -4i); }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(1_i, -4_i, "test.bsq", 2); Int tmp_0 = 1_i * -4_i; ᐸRuntimeᐳ::XInt::checkOverflowAddition(0_i, tmp_0, "test.bsq", 2); return 0_i + tmp_0; }');
        checkTestEmitMainFunction("public function main(): Nat { return +2n // 2n - 2n; }", 'Nat Mainᕒmain() { Nat tmp_0 = 2_n / 2_n; ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(tmp_0, 2_n, "test.bsq", 2); return tmp_0 - 2_n; }');
        checkTestEmitMainFunction("public function main(): Nat { return (+2n // 2n) - 2n; }", 'Nat Mainᕒmain() { Nat tmp_0 = 2_n / 2_n; ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(tmp_0, 2_n, "test.bsq", 2); return tmp_0 - 2_n; }');
        checkTestEmitMainFunction("public function main(): Nat { return +2n // (2n - 2n); }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowSubtraction(2_n, 2_n, "test.bsq", 2); Nat tmp_0 = 2_n - 2_n; ᐸRuntimeᐳ::XNat::checkDivisionByZero(tmp_0, "test.bsq", 2); return 2_n / tmp_0; }');
    });
});
