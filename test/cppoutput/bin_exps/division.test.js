"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe( "CPP Emit Evaluate --- Simple Division", () => {
    it("should cpp emit division simple", function () {
        runMainCode("public function main(): Nat { return 2n // 2n; }", "1_n");
        runMainCode("public function main(): Int { return 4i // 1i; }", "4_i");
        runMainCode("public function main(): BigNat { return 100N // 1N; }", "100_N");
        runMainCode("public function main(): BigInt { return -1I // -1I; }", "1_I");
        runMainCode("public function main(): Bool { return (2.0f // 1.0f) > 1.0f; }", "true");
    });
    it("should division error (undefined behaviour)", function () {
        runMainCodeError(`public function main(): Nat { return 2n // 0n; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): Int { return 2i // 0i; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): BigNat { return 3N // 0N; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): BigInt { return 1I // 0I; }`, "Over/underflow detected!\n");
        runMainCodeError(`public function main(): Float { return 1.0f // 0.0f; }`, "Over/underflow detected!\n");
    });
});