"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- map basic", () => {
    it("should do simple map", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.map(fn(x) => x + 2i); }', [['0i', 'List<Int>{}']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, z, 5i}.map(fn(x) => x + 2i); }', [['1i', 'List<Int>{2i, 3i, 7i}']], []);
        runTestSet('public function main(z: Int): List<Bool> { return List<Int>{1i, z, 5i}.map(pred(x) => x >= 0i); }', [['1i', 'List<Bool>{true, true, true}'], ['-1i', 'List<Bool>{true, false, true}']], []);
    });
});

describe ("List -- map index basic", () => {
    it("should do simple map index", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.mapIndex(fn(x, i) => x + i); }', [['0i', 'List<Int>{}']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, z, 5i}.mapIndex(fn(x, i) => x + i); }', [['1i', 'List<Int>{1i, 2i, 7i}']], []);
        runTestSet('public function main(z: Int): List<Bool> { return List<Int>{1i, z, 5i}.mapIndex(pred(x, i) => x >= 0i && x != i); }', [['1i', 'List<Bool>{true, true, true}'], ['-1i', 'List<Bool>{true, false, true}'], ['1i', 'List<Bool>{true, false, true}']], []);
    });
});

