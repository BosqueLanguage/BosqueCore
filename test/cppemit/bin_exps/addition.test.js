"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Simple addition", () => {
    it("should emit simple ops", function () {
        checkTestEmitMainFunction("public function main(): Nat { return 0n + 1n; }", 'Nat Mainᕒmain() { ᐸRuntimeᐳ::XNat::checkOverflowAddition(0_n, 1_n, "test.bsq", 2); return 0_n + 1_n; }');
        checkTestEmitMainFunction("public function main(): Int { return +2i + -2i; }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::XInt::checkOverflowAddition(2_i, -2_i, "test.bsq", 2); return 2_i + -2_i; }');
    });
});
