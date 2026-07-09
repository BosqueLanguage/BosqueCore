"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- map basic", () => {
    it("should do simple map", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.map<Int>(fn(x) => x + 2i); }', [['0i', 'List<Int>{ }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, z, 5i}.map<Int>(fn(x) => x + 2i); }', [['1i', 'List<Int>{ 3i, 3i, 7i }']], []);
        runTestSet('public function main(z: Int): List<Bool> { return List<Int>{1i, z, 5i}.map<Bool>(fn(x) => x >= 0i); }', [['1i', 'List<Bool>{ true, true, true }'], ['-1i', 'List<Bool>{ true, false, true }']], []);
    });
});

describe ("List -- map index basic", () => {
    it("should do simple map index", function () {
        runTestSet('public function main(z: Nat): List<Nat> { return List<Nat>{}.mapIdx<Nat>(fn(x, i) => x + i); }', [['0n', 'List<Nat>{ }']], []);
        runTestSet('public function main(z: Nat): List<Nat> { return List<Nat>{1n, z, 5n}.mapIdx<Nat>(fn(x, i) => x + i); }', [['1n', 'List<Nat>{ 1n, 2n, 7n }']], []);
        runTestSet('public function main(z: Nat): List<Bool> { return List<Nat>{1n, z, 5n}.mapIdx<Bool>(fn(x, i) => x > 0n && x != i); }', [['1n', 'List<Bool>{ true, false, true }'], ['0n', 'List<Bool>{ true, false, true }']], []);
    });
});

