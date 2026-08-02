"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- construct empty and isEmpty", () => {
    it("should create simple list", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.empty(); }', [['0i', 'true']], []); 
        runTestSet('public function main(z: Int): Bool { return List<Int>{1i}.empty(); }', [['0i', 'false']], []); 
    });

    it("should isSingle list", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.singleton(); }', [['0i', 'false']], []); 
        runTestSet('public function main(z: Int): Bool { return List<Int>{1i}.singleton(); }', [['0i', 'true']], []); 
        runTestSet('public function main(z: Int): Bool { return List<Int>{1i, 2i}.singleton(); }', [['0i', 'false']], []); 
    });

    it("should parse big list", function () {
        runTestSet('public function main(z: List<Int>): List<Int> { return z; }', [['List<Int>{}', 'List<Int>{ }'], ['List<Int>{1i, 2i, 3i}', 'List<Int>{ 1i, 2i, 3i }'], ['List<Int>{1i, 2i, 3i, 4i, 5i, 6i, 7i, 8i, 9i, 10i}', 'List<Int>{ 1i, 2i, 3i, 4i, 5i, 6i, 7i, 8i, 9i, 10i }'], ['List<Int>{1i, 2i, 3i, 4i, 5i, 6i, 7i, 8i, 9i, 10i, 11i, 12i, 13i, 14i, 15i, 16i, 17i, 18i, 19i, 20i}', 'List<Int>{ 1i, 2i, 3i, 4i, 5i, 6i, 7i, 8i, 9i, 10i, 11i, 12i, 13i, 14i, 15i, 16i, 17i, 18i, 19i, 20i }']], []);
    });
});

describe ("List -- immediate and size", () => {
    it("should create and size", function () {
        runTestSet('public function main(z: Int): Nat { return List<Int>{}.size(); }', [['0i', '0n']], []); 
        runTestSet('public function main(z: Int): Nat { return List<Int>{1i}.size(); }', [['0i', '1n']], []); 
        runTestSet('public function main(z: Int): Nat { return List<Int>{1i, 2i, 3i}.size(); }', [['0i', '3n']], []); 
    });

    it("should create and lastIndex", function () {
        runTestSet('public function main(z: Int): Nat { return List<Int>{1i}.lastIndex(); }', [['0i', '0n']], []); 
        runTestSet('public function main(z: Int): Nat { return List<Int>{1i, 2i, 3i}.lastIndex(); }', [['0i', '2n']], []); 
    });

    it("should error empty lastIndex", function () {
        runTestSet('public function main(z: Int): Nat { return List<Int>{}.lastIndex(); }', [], ['0i']); 
    });
});
