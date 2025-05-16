"use strict";

import { cppns, runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe( "CPP Evaluate --- Simple addition", () => {
    it("should cpp emit addition simple", function () {
        runMainCode("public function main(): Nat { return 2n + 2n; }", `return (2_n + 2_n);`);
    });
});