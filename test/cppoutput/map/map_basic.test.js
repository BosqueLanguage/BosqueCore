"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Map construct empty and isEmpty", () => {
    it("should create simple map", function () {
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.empty(); }', "true"); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i}.empty(); }', "false"); 
    });

    it("should isSingle simple map", function () {
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.isSingle(); }', "false"); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i}.isSingle(); }', "true"); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 5i => 0i}.isSingle(); }', "false"); 
    });
});

describe ("Map -- immediate and size", () => {
    it("should create and size", function () {
        runMainCode('public function main(): Nat { return Map<Int, Int>{}.size(); }', "0_n"); 
        runMainCode('public function main(): Nat { return Map<Int, Int>{1i => 2i}.size(); }', "1_n"); 
        runMainCode('public function main(): Nat { return Map<Int, Int>{1i => 2i, 3i => 4i}.size(); }', "2_n"); 
    });
});

describe ("Map -- has", () => {
    it("should create and size", function () {
        runMainCode('public function main(): Bool { return Map<Int, Int>{}.has(1i); }', "false"); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i}.has(1i); }', "true"); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 2i => 3i}.has(2i); }', "true"); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 5i => 3i}.has(2i); }', "false"); 
    });
});