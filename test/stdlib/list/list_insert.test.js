"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe ("List -- push/insert", () => {
    it("should get pushBack", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.pushBack(3i); }', [['1i', 'List<Int>{ 3i }']], []); 
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{z, 1i}.pushBack(z + 5i).pushBack(z + 10i); }', [['2i', 'List<Int>{ 2i, 1i, 7i, 12i }']], []);
    });

    it("should get pushFront", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{z}.pushFront(3i); }', [['1i', 'List<Int>{ 3i, 1i }']], []); 
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, z}.pushFront(z + 5i).pushFront(z + 10i); }', [['2i', 'List<Int>{ 12i, 7i, 1i, 2i }']], []); 
    });

    it("should get insert", function () {
        runTestSet('public function main(i: Nat): List<Int> { return List<Int>{}.insert(i, 1i); }', [['0n', 'List<Int>{ 1i }']], ['1n']); 
        runTestSet('public function main(i: Nat): List<Int> { return List<Int>{1i, 2i}.insert(i, 3i); }', [['0n', 'List<Int>{ 3i, 1i, 2i }'], ['1n', 'List<Int>{ 1i, 3i, 2i }'], ['2n', 'List<Int>{ 1i, 2i, 3i }']], ['5n']); 
        runTestSet('public function main(i: Nat): List<Int> { return List<Int>{1i, 2i, 3i}.insert(i, 4i); }', [['0n', 'List<Int>{ 4i, 1i, 2i, 3i }'], ['1n', 'List<Int>{ 1i, 4i, 2i, 3i }'], ['2n', 'List<Int>{ 1i, 2i, 4i, 3i }'], ['3n', 'List<Int>{ 1i, 2i, 3i, 4i }']], ['5n']); 
    });

    it("should mixed ops", function () {
        runTestSet('public function main(i: Nat): List<Int> { return List<Int>{1i, 2i}.pushFront(3i).pushBack(4i).insert(i, 5i); }', [['2n', 'List<Int>{ 3i, 1i, 5i, 2i, 4i }'], ['1n', 'List<Int>{ 3i, 5i, 1i, 2i, 4i }']], []);
        runTestSet('public function main(i: Nat): List<Int> { return List<Int>{1i, 2i}.insert(i, 5i).pushBack(4i).pushFront(3i).insert(i, 6i); }', [['0n', 'List<Int>{ 6i, 3i, 5i, 1i, 2i, 4i }'], ['1n', 'List<Int>{ 3i, 6i, 1i, 5i, 2i, 4i }']], []);

        runTestSet('public function main(i: Nat): List<Int> { return List<Int>{1i, 18i, 2i}.insert(i, 5i).insert(i, 6i).pushFront(3i).pushBack(4i); }', [['2n', 'List<Int>{ 3i, 1i, 18i, 6i, 5i, 2i, 4i }'], ['1n', 'List<Int>{ 3i, 1i, 6i, 5i, 18i, 2i, 4i }']], []);
    });
});
