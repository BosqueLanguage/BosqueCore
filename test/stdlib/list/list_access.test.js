"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- access", () => {
    it("should get single", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.single(); }', "1i"); 
    });

    it("should get back", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.back(); }', "1i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.back(); }', "2i"); 
    });

    it("should get front", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.front(); }', "1i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.front(); }', "1i"); 
    });

    it("should get index", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.get(0n); }', "1i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.get(0n); }', "1i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.get(1n); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.get(1n); }', "2i"); 
    });

    it("should fail get empty", function () {
        runMainCodeError('public function main(): Int { return List<Int>{}.back(); }', "Error -- !this.empty() @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{}.front(); }', "Error -- !this.empty() @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{}.get(0n); }', "Error -- i < this.size() @ list.bsq"); 
    });

    it("should fail get single", function () {
        runMainCodeError('public function main(): Int { return List<Int>{}.single(); }', "Error -- this.isSingleElement() @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{0i, 5i}.single(); }', "Error -- this.isSingleElement() @ list.bsq");
    });

    it("should fail get out-of-bounds", function () {
        runMainCodeError('public function main(): Int { return List<Int>{1i, 2i}.get(3n); }', "Error -- i < this.size() @ list.bsq");
    });

    it("should firstK/lastK", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i ,2i}.firstK(1n).size(); }', "1n"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.firstK(1n).front(); }', "1i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.firstK(2n).back(); }', "2i"); 

        runMainCode('public function main(): Nat { return List<Int>{1i ,2i}.lastK(2n).size(); }', "2n"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.lastK(1n).front(); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.lastK(1n).back(); }', "2i");

        runMainCode('public function main(): Nat { return List<Int>{1i ,2i}.firstK(0n).size(); }', "0n");
        runMainCode('public function main(): Nat { return List<Int>{}.firstK(0n).size(); }', "0n"); 
    });

    it("should fail firstK/lastK", function () {
        runMainCodeError('public function main(): Nat { return List<Int>{}.firstK(1n).size(); }', "Error -- n <= this.size() @ list.bsq"); 
        runMainCodeError('public function main(): Nat { return List<Int>{1i}.firstK(3n).size(); }', "Error -- n <= this.size() @ list.bsq"); 

        runMainCodeError('public function main(): Nat { return List<Int>{}.lastK(1n).size(); }', "Error -- n <= this.size() @ list.bsq"); 
        runMainCodeError('public function main(): Nat { return List<Int>{1i, 2i}.lastK(3n).size(); }', "Error -- n <= this.size() @ list.bsq"); 
    });
});
