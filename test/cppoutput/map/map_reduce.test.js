"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Map reduce simple", () => {
    it("should do simple bool reduce", function () {
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.reduce<Bool>(true, fn(acc, k, v) => acc && k > v); }', "true");
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.reduce<Bool>(false, fn(acc, k, v) => acc && v > 0i); }', "false");

        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 3i => 4i}.reduce<Bool>(true, fn(acc, k, v) => acc && v > 0i); }', "true");
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 3i => 0i}.reduce<Bool>(true, fn(acc, k, v) => acc && v > 0i); }', "false");
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 3i => 0i}.reduce<Bool>(true, fn(acc, k, v) => acc && k > 0i); }', "true");
    });

    it("should do simple int reduce", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{}.reduce<Int>(0i, fn(acc, k, v) => acc + v); }', "0_i");
        runMainCode('public function main(): Int { return Map<Int, Int>{}.reduce<Int>(5i, fn(acc, k, v) => acc + v); }', "5_i");

        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 3i => 0i}.reduce<Int>(0i, fn(acc, k, v) => acc + k); }', "4_i");
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 3i => 0i}.reduce<Int>(0i, fn(acc, k, v) => acc + v); }', "2_i");
    });
});
