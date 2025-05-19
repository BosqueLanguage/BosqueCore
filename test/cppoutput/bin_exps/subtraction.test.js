"use strict";

import { runMainCode, runMainCodeError, bsq_min_int, bsq_min_bigint } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe( "CPP Emit Evaluate --- Simple Subtraction", () => {
    it("should cpp emit subtraction simple", function () {
        runMainCode("public function main(): Nat { return 2n - 2n; }", "0_n");
        runMainCode("public function main(): Int { return 2i - -2i; }", "4_i");
        runMainCode("public function main(): BigNat { return 2N - 2N; }", "0_N");
        runMainCode("public function main(): BigInt { return 2I - 3I; }", "-1_I");
        runMainCode("public function main(): Bool { return (1.0f - 2.0f) < 0.0f; }", "true");
    });
    it("should subtraction error (underflow or undefined behaviour)", function () {
        runMainCodeError(`public function main(): Nat { return 1n - 2n; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): BigNat { return 1N - 2N; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): Int { return ${bsq_min_int}i - 1i; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): BigInt { return ${bsq_min_bigint}I - 1I; }`, "Over/underflow detected!\n");
    });
});