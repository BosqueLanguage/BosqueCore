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
});