"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Map set", () => {
    it("should set key", function () {
        runMainCode('public function main(): Nat { return Map<Int, Int>{1i => 0i}.set(1i, 2i).size(); }', "1n"); 

        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i}.set(1i, 2i).get(1i); }', "2i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i, 3i => 5i}.set(3i, 1i).get(3i); }', "1i");
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i, 3i => 5i}.set(1i, 4i).get(1i); }', "4i");
    });

    it("should fail set NOT exists", function () {
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.set(3i, 5i).get(1i); }', "Error -- this.has(k) @ map.bsq");
        runMainCodeError('public function main(): Int { return Map<Int, Int>{1i => 0i, 2i => 2i}.set(3i, 5i).get(1i); }', "Error -- this.has(k) @ map.bsq");
    });
});
