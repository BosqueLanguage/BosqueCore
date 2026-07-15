"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Map -- construct empty and isEmpty", () => {
    it("should create simple map", function () {
        runTestSet('public function main(z: Int): Bool { return Map<Int, Int>{}.empty(); }', [['0i', 'true']], []); 
        runTestSet('public function main(z: Int): Bool { return Map<Int, Int>{1i => 2i}.empty(); }', [['0i', 'false']], []); 
    });
});

describe ("Map -- immediate and size", () => {
    it("should create and size", function () {
        runTestSet('public function main(z: Int): Nat { return Map<Int, Int>{}.size(); }', [['0i', '0n']], []); 
        runTestSet('public function main(z: Int): Nat { return Map<Int, Int>{1i => 2i}.size(); }', [['0i', '1n']], []); 
        runTestSet('public function main(z: Int): Nat { return Map<Int, Int>{1i => 2i, 3i => 4i}.size(); }', [['0i', '2n']], []); 
    });
});

describe ("Map -- has", () => {
    it("should create and has", function () {
        runTestSet('public function main(z: Int): Bool { return Map<Int, Int>{}.has(1i); }', [['0i', 'false']], []); 
        runTestSet('public function main(z: Int): Bool { return Map<Int, Int>{z => 2i}.has(1i); }', [['0i', 'false'], ['1i', 'true']], []);
        runTestSet('public function main(z: Int): Bool { return Map<Int, Int>{1i => 2i, z => 4i}.has(3i); }', [['5i', 'false'], ['3i', 'true']], []);
    });
});

