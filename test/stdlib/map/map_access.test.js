"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Map -- access", () => {
    it("should get min", function () {
        runTestSet('public function main(z: Int): MapEntry<Int, Nat> { return Map<Int, Nat>{z => 2n}.min(); }', [['1i', 'MapEntry<Int, Nat>{ 1i, 2n }']], []);
        runTestSet('public function main(z: Int): MapEntry<Int, Nat> { return Map<Int, Nat>{z => 2n, 1i => 2n}.min(); }', [['2i', 'MapEntry<Int, Nat>{ 1i, 2n }'], ['0i', 'MapEntry<Int, Nat>{ 0i, 2n }']], []); 
    });

    it("should get max", function () {
        runTestSet('public function main(z: Int): MapEntry<Int, Nat> { return Map<Int, Nat>{z => 2n}.max(); }', [['1i', 'MapEntry<Int, Nat>{ 1i, 2n }']], []);
        runTestSet('public function main(z: Int): MapEntry<Int, Nat> { return Map<Int, Nat>{z => 2n, 1i => 2n}.max(); }', [['0i', 'MapEntry<Int, Nat>{ 1i, 2n }'], ['2i', 'MapEntry<Int, Nat>{ 2i, 2n }']], []);
    });

    it("should get key", function () {
        runTestSet('public function main(i: Int): Nat { return Map<Int, Nat>{1i => 2n}.get(i); }', [['1i', '2n']], ['0i']); 
        runTestSet('public function main(i: Int): Nat { return Map<Int, Nat>{1i => 2n, 3i => 4n}.get(i); }', [['3i', '4n'], ['1i', '2n']], ['5i']);
        runTestSet('public function main(i: Int): Nat { return Map<Int, Nat>{1i => 2n, 3i => 4n, 5i => 6n}.get(i); }', [['1i', '2n'], ['3i', '4n'], ['5i', '6n']], ['4i']);

        runTestSet('public function main(i: Int): Option<Nat> { return Map<Int, Nat>{1i => 2n, 3i => 4n}.tryGet(i); }', [['3i', 'some(4n)'], ['5i', 'none']], []);
    });

    it("should fail get empty", function () {
        runTestSet('public function main(z: Int): MapEntry<Int, Nat> { return Map<Int, Nat>{}.min(); }', [], ['0i']); 
        runTestSet('public function main(z: Int): MapEntry<Int, Nat> { return Map<Int, Nat>{}.max(); }', [], ['0i']); 
        runTestSet('public function main(z: Int): Nat { return Map<Int, Nat>{}.get(z); }', [], ['0i']); 
    });
});
