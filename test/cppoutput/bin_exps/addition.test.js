"use strict";

import { cppns, runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe( "CPP Evaluate --- Simple addition", () => {
    it("should cpp emit addition simple", function () {
        runMainCode("public function main(): Nat { return 2n + 2n; }", `return (2_n + 2_n);`);
        runMainCode("public function main(): Int { return 4i + 100i; }", `return (4_i + 100_i);`);
        runMainCode("public function main(): BigNat { return 2N + 1N; }", `return (2_N + 1_N);`);
        runMainCode("public function main(): BigInt { return 1I + 22I; }", `return (1_I + 22_I);`);
        runMainCode("public function main(): Float { return 1.0f + 1.0f; }", `return (1.0_f + 1.0_f);`);
    });
});