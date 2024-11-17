"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- map basic", () => {
    it("should do simple maps", function () {
        runMainCode('public function main(): Nat { return List<Int>{}.map<Bool>(fn(x) => x >= 0i).size(); }', [0n, "Nat"]);

        runMainCode('public function main(): Bool { return List<Int>{1i}.map<Bool>(fn(x) => x >= 0i).front(); }', [true, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{1i, -1i}.map<Bool>(fn(x) => x >= 0i).back(); }', [false, "Bool"]);
    });
});