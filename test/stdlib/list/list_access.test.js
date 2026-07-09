"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- access", () => {
    it("should get single", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{z}.single(); }', [['1i', '1i']], []);
        runTestSet('public function main(z: Int): Int { return List<Int>{}.single(); }', [], ['0i']);
        runTestSet('public function main(z: Int): Int { return List<Int>{0i, 5i}.single(); }', [], ['0i']);
    });

    it("should get back", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{z}.back(); }', [['1i', '1i']], []); 
        runTestSet('public function main(z: Int): Int { return List<Int>{1i, z}.back(); }', [['2i', '2i']], []); 
    });

    it("should get front", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{z}.front(); }', [['1i', '1i']], []); 
        runTestSet('public function main(z: Int): Int { return List<Int>{1i, z}.front(); }', [['1i', '1i']], []); 
    });

    it("should get index", function () {
        runTestSet('public function main(i: Nat): Int { return List<Int>{1i}.get(i); }', [['0n', '1i']], ['1n']); 
        runTestSet('public function main(i: Nat): Int { return List<Int>{1i, 2i}.get(i); }', [['0n', '1i'], ['1n', '2i']], ['5n']); 
        runTestSet('public function main(i: Nat): Int { return List<Int>{1i, 2i, 3i}.get(i); }', [['0n', '1i'], ['1n', '2i'], ['2n', '3i']], ['4n']); 
    });

    it("should fail get empty", function () {
        runTestSet('public function main(z: Int): Int { return List<Int>{}.back(); }', [], ['0i']); 
        runTestSet('public function main(z: Int): Int { return List<Int>{}.front(); }', [], ['0i']); 
        runTestSet('public function main(): Int { return List<Int>{}.get(0n); }', [], ['0i']); 
    });
});
