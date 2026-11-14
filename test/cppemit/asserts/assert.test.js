"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- simple abort", () => {
    it("should emit simple abort", function () {
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b) { abort; } return 1i; }", 'Int Mainᕒmain(Bool b) { if(b) { ᐸRuntimeᐳ::bsq_abort("test.bsq", 2, nullptr, nullptr); } return 1_i; }');
    });
});

describe ("CPPEmit -- simple assert", () => {
    it("should emit simple assert", function () {
        checkTestEmitMainFunction("public function main(x: Int): Int { assert x > 0i; return 1i; }", 'Int Mainᕒmain(Int x) { ᐸRuntimeᐳ::bsq_assert((bool)(x > 0_i), "test.bsq", 2, nullptr, "Assertion Failed"); return 1_i; }');
        checkTestEmitMainFunction("public function main(x: Int): Int { assert debug true; return 1i; }", "Int Mainᕒmain(Int x) { return 1_i; }");

        checkTestEmitMainFunction("public function main(x: Int): Int { assert true & x > 0i; return 1i; }", 'Int Mainᕒmain(Int x) { ᐸRuntimeᐳ::bsq_assert((bool)(x > 0_i), "test.bsq", 2, nullptr, "Assertion Failed"); return 1_i; }');
    });
});
