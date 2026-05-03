"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- construct empty and isEmpty", () => {
    it("should create simple list", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.empty(); }', [['0i', 'true']], []); 
        runTestSet('public function main(z: Int): Bool { return List<Int>{1i}.empty(); }', [['0i', 'false']], []); 
    });

    it("should isSingle list", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.isSingle(); }', [['0i', 'false']], []); 
        runTestSet('public function main(z: Int): Bool { return List<Int>{1i}.isSingle(); }', [['0i', 'true']], []); 
        runTestSet('public function main(z: Int): Bool { return List<Int>{1i, 2i}.isSingle(); }', [['0i', 'false']], []); 
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
