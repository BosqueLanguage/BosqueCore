"use strict";

import { runMainCode, runMainCodeError, bsq_max_nat, bsq_max_int,  bsq_max_bignat, bsq_max_bigint } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe( "CPP Emit Evaluate --- Simple addition", () => {
    it("should cpp emit addition simple", function () {
        runMainCode("public function main(): Nat { return 2n + 2n; }", "4_n");
        runMainCode("public function main(): Int { return 4i + 100i; }", "104_i");
        runMainCode("public function main(): BigNat { return 2N + 1N; }", "3_N");
        runMainCode("public function main(): BigInt { return 1I + 22I; }", "23_I");
        runMainCode("public function main(): Bool { return (1.0f + 1.0f) > 1.0f; }", "true");
    });
    it("should addition error (overflow or undefined behaviour)", function () {
        runMainCodeError(`public function main(): Nat { return ${bsq_max_nat}n + 1n; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): Int { return ${bsq_max_int}i + 1i; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): BigNat { return ${bsq_max_bignat}N + 1N; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): BigInt { return ${bsq_max_bigint}I + 1I; }`, "Over/underflow detected!\n");
    });
});