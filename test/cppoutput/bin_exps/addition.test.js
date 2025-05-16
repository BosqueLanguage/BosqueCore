"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe( "CPP Evaluate --- Simple addition", () => {
    it("should cpp emit addition simple", function () {
        runMainCode("public function main(): Nat { return 2n + 2n; }", "4_n");
        runMainCode("public function main(): Int { return 4i + 100i; }", "104_i");
        runMainCode("public function main(): BigNat { return 2N + 1N; }", "3_N");
        runMainCode("public function main(): BigInt { return 1I + 22I; }", "23_I");
        runMainCode("public function main(): Bool { return (1.0f + 1.0f) > 1.0f; }", "true");
    });
    it("should addition error (overflow or undefined behaviour)", function () {
        runMainCodeError("public function main(): Nat { return 4611686018427387903n + 1n; }", "Over/underflow detected!\n");
    });
});