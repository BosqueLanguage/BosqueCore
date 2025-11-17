"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Map -- delete", () => {
    it("should delete key", function () {
        runMainCode('public function main(): Nat { return Map<Int, Bool>{ 1i => true, 2i => false }.delete(2i).size(); }', "1n"); 
        runMainCode('public function main(): Nat { return Map<Int, Bool>{ 4i => true, 1i => false }.insert(2i, false).delete(4i).size(); }', "2n"); 
        runMainCode('public function main(): Bool { return Map<Int, Bool>{ 1i => true, 2i => false }.delete(2i).get(1i); }', "true"); 
        runMainCode('public function main(): Nat { return Map<Int, Bool>{ 2i => true, 3i => true }.insert(4i, true).insert(5i, false).insert(1i, true).delete(1i).delete(3i).size(); }', "3n"); 
        runMainCode('public function main(): Bool { return Map<Int, Bool>{ 1i => true, 2i => false }.delete(2i).get(1i) === true; }', "true"); 
        runMainCode('public function main(): Bool { return Map<Int, Bool>{ 1i => true, 2i => false }.insert(3i, false).delete(2i).get(1i) === true; }', "true"); 
        runMainCode('public function main(): Nat { return Map<Int, Bool>{ 2i => true, 3i => true }.insert(4i, true).insert(5i, false).insert(1i, true).insert(8i, false).delete(1i).delete(3i).delete(8i).size(); }', "3n");
        runMainCode('public function main(): Nat { return Map<Int, Bool>{ 2i => true, 3i => true }.insert(4i, true).insert(1i, false).insert(11i, false).insert(10i, true).insert(6i, false).insert(7i, true).insert(5i, false).delete(2i).size(); }', "8n")
    });

    it("should delete to empty", function () {
        runMainCode('public function main(): Bool { return Map<Int, Bool>{ 1i => true }.delete(1i).size() === 0n; }', "true"); 
        runMainCode('public function main(): Bool { return Map<Int, Int>{ 7i => 2i}.insert(3i, 1i).delete(3i).delete(7i).size() === 0n; }', "true"); 
    });

    it("should fail delete doesnt exist", function () {
        runMainCodeError('public function main(): Bool { return Map<Int, Bool>{ 1i => true, 2i => false }.delete(3i).size() === 1n; }', "Error -- this.has(k) @ map.bsq"); 
        runMainCodeError('public function main(): Bool { return Map<Int, Bool>{ 1i => true, 2i => false }.insert(3i, true).delete(1i).get(1i) === true; }', "Error -- this.has(k) @ map.bsq"); 
    });
});