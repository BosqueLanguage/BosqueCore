"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate List -- construct empty and isEmpty", () => {
    it("should create simple list", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.empty(); }', "true"); 
        runMainCode('public function main(): Bool { return List<Int>{1i}.empty(); }', "false"); 
    });

    it("should isSingle list", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.isSingle(); }', "false"); 
        runMainCode('public function main(): Bool { return List<Int>{1i}.isSingle(); }', "true"); 
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i}.isSingle(); }', "false"); 
    });
});

describe ("CPP Emit Evaluate List -- immediate and size", () => {
    it("should create and size", function () {
        runMainCode('public function main(): Nat { return List<Int>{}.size(); }', "0_n"); 
        runMainCode('public function main(): Nat { return List<Int>{1i}.size(); }', "1_n"); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.size(); }', "3_n"); 
    });

    it("should create and lastIndex", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i}.lastIndex(); }', "0_n"); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.lastIndex(); }', "2_n"); 
    });

/*
    it("smt should error empty lastIndex", function () {
        runMainCode('public function main(): Nat { return List<Int>{}.lastIndex(); }', ""); 
    });
*/
});

