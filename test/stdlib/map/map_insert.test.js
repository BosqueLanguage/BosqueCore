"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe ("Map -- add/set/insert", () => {
    it("should insert", function () {
        runTestSet('public function main(z: Int): Map<Int, Nat> { return Map<Int, Nat>{}.insert(z, 4n); }', [['1i', 'Map<Int, Nat>{ 1i => 4n }']], []); 
        runTestSet('public function main(z: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 2n}.insert(z, 4n); }', [['2i', 'Map<Int, Nat>{ 1i => 2n, 2i => 4n }'], ['0i', 'Map<Int, Nat>{ 0i => 4n, 1i => 2n }'], ['1i', 'Map<Int, Nat>{ 1i => 4n }']], []);
    });

    it("should set", function () {
        runTestSet('public function main(z: Int): Map<Int, Nat> { return Map<Int, Nat>{ 2i => 2n, 4i => 3n }.set(z, 5n); }', [['2i', 'Map<Int, Nat>{ 2i => 5n, 4i => 3n }'], ['4i', 'Map<Int, Nat>{ 2i => 2n, 4i => 5n }']], ['1i']);
    });

    it("should add", function () {
        runTestSet('public function main(i: Int): Map<Int, Nat> { return Map<Int, Nat>{}.add(i, 1n); }', [['0i', 'Map<Int, Nat>{ 0i => 1n }']], []);
        runTestSet('public function main(i: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 2i => 2n}.add(i, 3n); }', [['0i', 'Map<Int, Nat>{ 0i => 3n, 1i => 1n, 2i => 2n }'], ['11i', 'Map<Int, Nat>{ 1i => 1n, 2i => 2n, 11i => 3n }']], ['2i']); 
        runTestSet('public function main(i: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 2i => 2n, 3i => 3n}.add(i, 4n); }', [['0i', 'Map<Int, Nat>{ 0i => 4n, 1i => 1n, 2i => 2n, 3i => 3n }'], ['5i', 'Map<Int, Nat>{ 1i => 1n, 2i => 2n, 3i => 3n, 5i => 4n }']], ['3i']); 
    });

    it("should mixed ops", function () {
        runTestSet('public function main(i: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 2i => 2n}.add(3i, 3n).add(4i, 4n).insert(i, 5n); }', [['2i', 'Map<Int, Nat>{ 1i => 1n, 2i => 5n, 3i => 3n, 4i => 4n }'], ['11i', 'Map<Int, Nat>{ 1i => 1n, 2i => 2n, 3i => 3n, 4i => 4n, 11i => 5n }']], []);
        runTestSet('public function main(i: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 2i => 2n}.set(i, 5n).add(4i, 4n).set(2i, 100n).insert(i + 1i, 6n); }', [['2i', 'Map<Int, Nat>{ 1i => 1n, 2i => 100n, 3i => 6n, 4i => 4n }']], ['0i']);

        runTestSet('public function main(i: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 18i => 18n, 2i => 2n}.insert(i, 5n).insert(i + 1i, 6n).add(3i, 3n).add(4i, 4n); }', [['0i', 'Map<Int, Nat>{ 0i => 5n, 1i => 6n, 2i => 2n, 3i => 3n, 4i => 4n, 18i => 18n }'], ['5i', 'Map<Int, Nat>{ 1i => 1n, 2i => 2n, 3i => 3n, 4i => 4n, 5i => 5n, 6i => 6n, 18i => 18n }']], ['2i']);
    });
});
