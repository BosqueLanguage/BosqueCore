"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Map -- construct empty and isEmpty", () => {
    it("should create simple map", function () {
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.empty(); }', [true, "Bool"]); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i}.empty(); }', [false, "Bool"]); 
    });

    it("should isSingle simple map", function () {
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.isSingleElement(); }', [false, "Bool"]); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i}.isSingleElement(); }', [true, "Bool"]); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 5i => 0i}.isSingleElement(); }', [false, "Bool"]); 
    });
});

describe ("Map -- immediate and size", () => {
    it("should create and size", function () {
        runMainCode('public function main(): Nat { return Map<Int, Int>{}.size(); }', [0n, "Nat"]); 
        runMainCode('public function main(): Nat { return Map<Int, Int>{1i => 2i}.size(); }', [1n, "Nat"]); 
        runMainCode('public function main(): Nat { return Map<Int, Int>{1i => 2i, 3i => 4i}.size(); }', [2n, "Nat"]); 
    });
});

describe ("Map -- has", () => {
    it("should create and size", function () {
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.has(1i); }', [false, "Bool"]); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i}.has(1i); }', [true, "Bool"]); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 2i => 3i}.has(2i); }', [true, "Bool"]); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 5i => 3i}.has(2i); }', [false, "Bool"]); 
    });
});
