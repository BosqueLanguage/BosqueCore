"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Map reduce simple", () => {
    it("should do simple bool reduce", function () {
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.reduce<Bool>(fn(acc, k, v) => acc && k > v, true); }', "true");
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.reduce<Bool>(fn(acc, k, v) => acc && v > 0i, false); }', "false");

        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 3i => 4i}.reduce<Bool>(fn(acc, k, v) => acc && v > 0i, true); }', "true");
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 3i => 0i}.reduce<Bool>(fn(acc, k, v) => acc && v > 0i, true); }', "false");
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 3i => 0i}.reduce<Bool>(fn(acc, k, v) => acc && k > 0i, true); }', "true");
    });

    it("should do simple int reduce", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{}.reduce<Int>(fn(acc, k, v) => acc + v, 0i); }', "0_i");
        runMainCode('public function main(): Int { return Map<Int, Int>{}.reduce<Int>(fn(acc, k, v) => acc + v, 5i); }', "5_i");

        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 3i => 0i}.reduce<Int>(fn(acc, k, v) => acc + k, 0i); }', "4_i");
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 3i => 0i}.reduce<Int>(fn(acc, k, v) => acc + v, 0i); }', "2_i");
    });
});
