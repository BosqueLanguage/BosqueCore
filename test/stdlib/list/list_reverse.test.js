"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- reverse", () => {
    it("should reverse", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.reverse().empty(); }', "true");

        runMainCode('public function main(): Int { return List<Int>{1i}.reverse().front(); }', "1i");

        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.reverse().size(); }', "3n");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.reverse().front(); }', "3i");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.reverse().back(); }', "1i");
    });
});
