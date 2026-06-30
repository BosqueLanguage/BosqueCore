"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- ranges", () => {
    it("should create Int ranges", function () {
        runTestSet('public function main(z: Int): List<Int> { return List::rangeOfInt(3i, z); }', [['3i', 'List<Int>{ }'], ['4i', 'List<Int>{ 3i }'], ['6i', 'List<Int>{ 3i, 4i, 5i }'], ['8i', 'List<Int>{ 3i, 4i, 5i, 6i, 7i }'], ['11i', 'List<Int>{ 3i, 4i, 5i, 6i, 7i, 8i, 9i, 10i }']], ['-1i']); 
        runTestSet('public function main(z: Int): List<Int> { return List::rangeOfInt(z, 1i); }', [['0i', 'List<Int>{ 0i }'], ['-1i', 'List<Int>{ -1i, 0i }']], ['5i']);  
    });

    it("should create Nat ranges", function () {
        runTestSet('public function main(z: Nat): List<Nat> { return List::rangeOfNat(3n, z); }', [['3n', 'List<Nat>{ }'], ['4n', 'List<Nat>{ 3n }'], ['6n', 'List<Nat>{ 3n, 4n, 5n }'], ['8n', 'List<Nat>{ 3n, 4n, 5n, 6n, 7n }'], ['11n', 'List<Nat>{ 3n, 4n, 5n, 6n, 7n, 8n, 9n, 10n }']], ['1n']);
    });
});

describe ("List -- zip", () => {
    it("should zip lists", function () {
        runTestSet('public function main(z: Int): List<(|Int, Nat|)> { return List::zip<Int, Nat>(List::rangeOfInt(0i, z), List::rangeOfNat(0n, 0n)); }', [['0i', 'List<(|Int, Nat|)>{ }']], ['1i']);
        runTestSet('public function main(z: Int): List<(|Int, Nat|)> { return List::zip<Int, Nat>(List::rangeOfInt(0i, z), List::rangeOfNat(0n, 3n)); }', [['3i', 'List<(|Int, Nat|)>{ (| 0i, 0n |), (| 1i, 1n |), (| 2i, 2n |) }']], []);
        runTestSet('public function main(z: Int): List<(|Int, Nat|)> { return List::zip<Int, Nat>(List::rangeOfInt(0i, z), List::rangeOfNat(0n, 6n)); }', [['6i', 'List<(|Int, Nat|)>{ (| 0i, 0n |), (| 1i, 1n |), (| 2i, 2n |), (| 3i, 3n |), (| 4i, 4n |), (| 5i, 5n |) }']], []);

        runTestSet('public function main(z: Int): List<(|Int, Option<Nat>|)> { return List::zip<Int, Option<Nat>>(List::rangeOfInt(0i, z), List<Option<Nat>>{none, some(1n), none}); }', [['3i', 'List<(|Int, Option<Nat>|)>{ (| 0i, none |), (| 1i, some(1n) |), (| 2i, none |) }']], []);
    });
});

