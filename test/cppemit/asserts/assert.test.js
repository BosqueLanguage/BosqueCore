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

        checkTestEmitMainFunction("public function main(x: Int): Int { validate x > 0i || true; return 1i; }", "Int Mainᕒmain(Int x) { return 1_i; }");
    });
});

describe ("CPPEmit -- simple validate", () => {
    it("should emit simple validate", function () {
        checkTestEmitMainFunction("public function main(x: Int): Int { validate x == 3i; return 1i; }", 'Int Mainᕒmain(Int x) { ᐸRuntimeᐳ::bsq_validate((bool)(x == 3_i), "test.bsq", 2, nullptr, "Validation Failed"); return 1_i; }');
        checkTestEmitMainFunction("public function main(x: Int): Int { validate x > 0i || false; return 1i; }", 'Int Mainᕒmain(Int x) { ᐸRuntimeᐳ::bsq_validate((bool)(x > 0_i), "test.bsq", 2, nullptr, "Validation Failed"); return 1_i; }');

        checkTestEmitMainFunction("public function main(x: Int): Int { validate x > (1i + 2i); return 1i; }", 'Int Mainᕒmain(Int x) { ᐸRuntimeᐳ::XInt::checkOverflowAddition(1_i, 2_i, "test.bsq", 2); ᐸRuntimeᐳ::bsq_validate((bool)(x > (1_i + 2_i)), "test.bsq", 2, nullptr, "Validation Failed"); return 1_i; }');
        checkTestEmitMainFunction("public function main(b: Bool): Int { validate['ec-0'] b; return 1i; }", 'Int Mainᕒmain(Bool b) { ᐸRuntimeᐳ::bsq_validate((bool)(b), "test.bsq", 2, "ec-0", "Validation Failed"); return 1_i; }');
    });
});
