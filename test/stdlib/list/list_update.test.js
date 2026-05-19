"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe ("List -- set", () => {
    it("should set", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.set(0n, z); }', [], ['0n']); 
        runTestSet('public function main(ii: Nat): List<Int> { return List<Int>{3i, 1i, 8i}.set(ii, 5i); }', [['0n', 'List<Int>{ 5i, 1i, 8i }'], ['1n', 'List<Int>{ 3i, 5i, 8i }'], ['2n', 'List<Int>{ 3i, 1i, 5i }']], ['3n']);
    });
});
