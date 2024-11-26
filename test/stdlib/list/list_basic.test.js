"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- construct empty and isEmpty", () => {
    it("should create simple list", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.empty(); }', [true, "Bool"]); 
        runMainCode('public function main(): Bool { return List<Int>{1i}.empty(); }', [false, "Bool"]); 
    });
});

describe ("List -- immediate and size", () => {
    it("should create and size", function () {
        runMainCode('public function main(): Nat { return List<Int>{}.size(); }', [0n, "Nat"]); 
        runMainCode('public function main(): Nat { return List<Int>{1i}.size(); }', [1n, "Nat"]); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.size(); }', [3n, "Nat"]); 
    });
});

