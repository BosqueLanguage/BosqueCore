"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Map map basic", () => {
    it("should do simple maps", function () {
        runMainCode('public function main(): Nat { return Map<Int, Bool>{}.map<Bool>(fn(k, v) => v).size(); }', "0n");

        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 1i}.map<Bool>(fn(k, v) => k == v).get(1i); }', "true");
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 1i, 2i => 1i}.map<Bool>(fn(k, v) => k == v).get(1i); }', "true");
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 1i, 2i => 1i}.map<Bool>(fn(k, v) => k == v).get(2i); }', "false");
    });
});
