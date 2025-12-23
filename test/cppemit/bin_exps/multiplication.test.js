"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Simple multiplication", () => {
    it("should emit simple ops", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 1n * 1n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowMultiplication(1_n, 1_n, "test.bsq", 2); return 1_n * 1_n; }');
        checkTestEmitMainFunction("public function main(): Int { return 2i * -2i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowMultiplication(2_i, -2_i, "test.bsq", 2); return 2_i * -2_i; }');
    });
});
