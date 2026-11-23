"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe ("Map -- remove/clear", () => {
    it("should remove", function () {
        runTestSet('public function main(z: Int): Map<Int, Nat> { return Map<Int, Nat>{}.remove(z); }', [], ['10i']);
        
        runTestSet('public function main(z: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 4i => 4n, 5i => 5n}.remove(z); }', [['1i', 'Map<Int, Nat>{ 4i => 4n, 5i => 5n }'], ['4i', 'Map<Int, Nat>{ 1i => 1n, 5i => 5n }'], ['5i', 'Map<Int, Nat>{ 1i => 1n, 4i => 4n }']], ['10i']);
        runTestSet('public function main(z: Int): Map<Int, Nat> { var s = Map<Int, Nat>{1i => 1n, 4i => 4n, 5i => 5n}; ref s.remove(z); return s; }', [['1i', 'Map<Int, Nat>{ 4i => 4n, 5i => 5n }'], ['4i', 'Map<Int, Nat>{ 1i => 1n, 5i => 5n }'], ['5i', 'Map<Int, Nat>{ 1i => 1n, 4i => 4n }']], ['10i']); 
    });

    it("should clear", function () {
        runTestSet('public function main(z: Int): Map<Int, Nat> { return Map<Int, Nat>{}.clear(z); }', [['1i', 'Map<Int, Nat>{ }']], []);
        
        runTestSet('public function main(z: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 4i => 4n, 5i => 5n}.clear(z); }', [['1i', 'Map<Int, Nat>{ 4i => 4n, 5i => 5n }'], ['4i', 'Map<Int, Nat>{ 1i => 1n, 5i => 5n }'], ['5i', 'Map<Int, Nat>{ 1i => 1n, 4i => 4n }'], ['10i', 'Map<Int, Nat>{ 1i => 1n, 4i => 4n, 5i => 5n }']], []);
        runTestSet('public function main(z: Int): Map<Int, Nat> { var s = Map<Int, Nat>{1i => 1n, 4i => 4n, 5i => 5n}; ref s.clear(z); return s; }', [['1i', 'Map<Int, Nat>{ 4i => 4n, 5i => 5n }'], ['4i', 'Map<Int, Nat>{ 1i => 1n, 5i => 5n }'], ['5i', 'Map<Int, Nat>{ 1i => 1n, 4i => 4n }'], ['10i', 'Map<Int, Nat>{ 1i => 1n, 4i => 4n, 5i => 5n }']], []); 
    });

    it("should mixed ops", function () {
        runTestSet('public function main(i: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 2i => 2n, 4i => 4n}.remove(2i).clear(i); }', [['2i', 'Map<Int, Nat>{ 1i => 1n, 4i => 4n }'], ['1i', 'Map<Int, Nat>{ 4i => 4n }'], ['11i', 'Map<Int, Nat>{ 1i => 1n, 4i => 4n }']], []);
        runTestSet('public function main(i: Int): Map<Int, Nat> { return Map<Int, Nat>{1i => 1n, 2i => 2n, 0i => 0n, 9i => 9n}.remove(i).clear(2i); }', [['0i', 'Map<Int, Nat>{ 1i => 1n, 9i => 9n }'], ['1i', 'Map<Int, Nat>{ 0i => 0n, 9i => 9n }'], ['2i', 'Map<Int, Nat>{ 0i => 0n, 1i => 1n, 9i => 9n }']], ['2i']);
    });
});
