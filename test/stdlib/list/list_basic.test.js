"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- construct empty and isEmpty", () => {
    it("should create simple list", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.empty(); }', "true"); 
        runMainCode('public function main(): Bool { return List<Int>{1i}.empty(); }', "false"); 
    });

    it("should isSingle list", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.isSingleElement(); }', "false"); 
        runMainCode('public function main(): Bool { return List<Int>{1i}.isSingleElement(); }', "true"); 
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i}.isSingleElement(); }', "false"); 
    });
});

describe ("List -- immediate and size", () => {
    it("should create and size", function () {
        runMainCode('public function main(): Nat { return List<Int>{}.size(); }', "0n"); 
        runMainCode('public function main(): Nat { return List<Int>{1i}.size(); }', "1n"); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.size(); }', "3n"); 
    });

    it("should create and lastIndex", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i}.lastIndex(); }', "0n"); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.lastIndex(); }', "2n"); 
    });

    it("should error empty lastIndex", function () {
        runMainCodeError('public function main(): Nat { return List<Int>{}.lastIndex(); }', "Error -- !this.empty() @ list.bsq"); 
    });
});

