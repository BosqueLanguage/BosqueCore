"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe( "CPP Evaluate -- Simple numeric sign", () => {
    it("should exec (simplfy) simple sign", function () {
        runMainCode("public function main(): Int { return -(3i); }", "-3_i");
        runMainCode("public function main(): Nat { return +(12n); }", "12_n");
        runMainCode("public function main(): BigInt { return -3I; }", "-3_I");
        runMainCode("public function main(): BigNat { return +(12N); }", "12_N");
        runMainCode("public function main(): Bool { return ( -2.0f < 0.0f ); }", "true");
    });
    it("should exec simple sign", function() {
        runMainCode("public function main(): Int { let x = 3i; return -x; }", "-3_i");
        runMainCode("public function main(): Nat { let x = 12n; return +x; }", "12_n");
        runMainCode("public function main(): BigInt { let x = 3I; return -x; }", "-3_I");
        runMainCode("public function main(): BigNat { let x = 12N; return +x; }", "12_N");
        runMainCode("public function main(): Bool { let x = 2.0f; return ( -x < 0.0f ); }", "true");
    });
});
