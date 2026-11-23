"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe ("Set -- remove/clear", () => {
    it("should remove", function () {
        runTestSet('public function main(z: Int): Set<Int> { return Set<Int>{1i, 4i, 5i}.remove(z); }', [['1i', 'Set<Int>{ 4i, 5i }'], ['4i', 'Set<Int>{ 1i, 5i }'], ['5i', 'Set<Int>{ 1i, 4i }']], ['10i']);
        runTestSet('public function main(z: Int): Set<Int> { let s = Set<Int>{1i, 4i, 5i}; ref s.remove(z); return s; }', [['1i', 'Set<Int>{ 4i, 5i }'], ['4i', 'Set<Int>{ 1i, 5i }'], ['5i', 'Set<Int>{ 1i, 4i }']], ['10i']); 
    });

    it("should clear", function () {
        runTestSet('public function main(z: Int): Set<Int> { return Set<Int>{1i, 4i, 5i}.clear(z); }', [['1i', 'Set<Int>{ 4i, 5i }'], ['4i', 'Set<Int>{ 1i, 5i }'], ['5i', 'Set<Int>{ 1i, 4i }'], ['10i', 'Set<Int>{ 1i, 4i, 5i }']], []);
        runTestSet('public function main(z: Int): Set<Int> { let s = Set<Int>{1i, 4i, 5i}; ref s.clear(z); return s; }', [['1i', 'Set<Int>{ 4i, 5i }'], ['4i', 'Set<Int>{ 1i, 5i }'], ['5i', 'Set<Int>{ 1i, 4i }'], ['10i', 'Set<Int>{ 1i, 4i, 5i }']], []); 
    });

    it("should mixed ops", function () {
        runTestSet('public function main(i: Int): Set<Int> { return Set<Int>{1i, 2i, 4i}.remove(2i).clear(i); }', [['2i', 'Set<Int>{ 1i, 4i }'], ['1i', 'Set<Int>{ 4i }'], ['11i', 'Set<Int>{ 1i, 4i}']], []);
        runTestSet('public function main(i: Int): Set<Int> { return Set<Int>{1i, 2i, 0i, 9i}.remove(i).clear(2i); }', [['0i', 'Set<Int>{ 1i, 9i }'], ['1i', 'Set<Int>{ 0i, 9i }'], ['2i', 'Set<Int>{ 1i, 0i, 9i }']], ['2i']);
    });
});
