"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Set -- construct empty and isEmpty", () => {
    it("should create simple set", function () {
        runTestSet('public function main(z: Int): Bool { return Set<Int>{}.empty(); }', [['0i', 'true']], []); 
        runTestSet('public function main(z: Int): Bool { return Set<Int>{1i}.empty(); }', [['0i', 'false']], []); 
    });
});

describe ("Set -- immediate and size", () => {
    it("should create and size", function () {
        runTestSet('public function main(z: Int): Nat { return Set<Int>{}.size(); }', [['0i', '0n']], []); 
        runTestSet('public function main(z: Int): Nat { return Set<Int>{1i}.size(); }', [['0i', '1n']], []); 
        runTestSet('public function main(z: Int): Nat { return Set<Int>{1i, 3i}.size(); }', [['0i', '2n']], []); 
    });
});

describe ("Set -- big parse", () => {
    it("should test big parsing", function () {
        runTestSet('public function main(z: Set<Int>): Set<Int> { return z; }', [['Set<Int>{ }', 'Set<Int>{ }'], ['Set<Int>{ 0i, 1i, 2i, 3i, 4i }', 'Set<Int>{ 0i, 1i, 2i, 3i, 4i }']], []);
    });
});

describe ("Set -- has", () => {
    it("should create and has", function () {
        runTestSet('public function main(z: Int): Bool { return Set<Int>{}.has(1i); }', [['0i', 'false']], []); 
        runTestSet('public function main(z: Int): Bool { return Set<Int>{z}.has(1i); }', [['0i', 'false'], ['1i', 'true']], []);
        runTestSet('public function main(z: Int): Bool { return Set<Int>{1i, z}.has(3i); }', [['5i', 'false'], ['3i', 'true']], []);
    });
});

