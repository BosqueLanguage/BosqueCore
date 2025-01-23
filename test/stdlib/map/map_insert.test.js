"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Map -- insert", () => {
    it("should insert key", function () {
        runMainCode('public function main(): Nat { return Map<Int, Int>{1i => 0i}.insert(0i, 2i).size(); }', "2n"); 

        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i}.insert(0i, 2i).get(0i); }', "2i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i}.insert(0i, 2i).get(1i); }', "0i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i}.insert(2i, 2i).get(2i); }', "2i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i}.insert(2i, 2i).get(1i); }', "0i"); 

        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i, 3i => 5i}.insert(2i, 2i).get(2i); }', "2i");
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i, 3i => 5i}.insert(2i, 2i).get(3i); }', "5i");
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i, 3i => 5i}.insert(0i, 2i).get(0i); }', "2i");
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i, 3i => 5i}.insert(0i, 2i).get(3i); }', "5i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i, 3i => 5i}.insert(5i, 2i).get(5i); }', "2i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 0i, 3i => 5i}.insert(5i, 2i).get(3i); }', "5i"); 
    });

    it("should insert empty", function () {
        runMainCode('public function main(): Nat { return Map<Int, Int>{}.insert(0i, 1i).size(); }', "1n"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{}.insert(0i, 1i).get(0i); }', "1i"); 
    });

    it("should fail insert exists", function () {
        runMainCodeError('public function main(): Int { return Map<Int, Int>{1i => 0i, 2i => 2i}.insert(2i, 5i).get(1i); }', "Error -- !this.has(k) @ map.bsq");
    });
});
