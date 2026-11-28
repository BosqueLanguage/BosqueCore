"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- mapreduce op", () => {
    it("should mapreduce list", function () {
        runTestSet(`public function main(z: Int): Bool { return List<Int>{}.mapreduce<Bool>(fn(v: Int) => v >= 1i, fn(acc: Bool, v: Bool) => acc & v, true); }`, [['1i', 'true']], []);  
        runTestSet(`public function main(z: Int): Bool { return List<Int>{1i, z, 3i}.mapreduce<Bool>(fn(v: Int) => v >= 1i, fn(acc: Bool, v: Bool) => acc & v, true); }`, [['1i', 'true'], ['0i', 'false']], []);  
    });
}); 

describe ("List -- flatmap basic", () => {
    it("should do simple flatmap", function () {
        runTestSet('public function main(z: Int): List<Bool> { return List<Int>{1i, z, 5i}.flatmap<Bool>(fn(x) => List<Bool>{ x == 1i, x >= 0i }); }', [['1i', 'List<Bool>{ true, true, true, true, false, true }'], ['-1i', 'List<Bool>{ true, true, false, false, false, true }']], []);
    });

    it("should do simple flatmapIdx", function () {
        runTestSet('public function main(z: Nat): List<Nat> { return List<Nat>{1n, z, 5n}.flatmapIdx<Nat>(fn(x, i) => List<Nat>{ x, i, x + i }); }', [['3n', 'List<Nat>{ 1n, 0n, 1n, 3n, 1n, 4n, 5n, 2n, 7n }']], []);
    });
});
