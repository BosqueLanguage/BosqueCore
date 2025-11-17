"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- filter basic", () => {
    it("should do simple filters", function () {
        runMainCode('public function main(): Nat { return List<Int>{}.filter(pred(x) => x >= 0i).size(); }', "0n");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.filter(pred(x) => false).size(); }', "0n");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.filter(pred(x) => true).size(); }', "3n");

        runMainCode('public function main(): Int { return List<Int>{1i}.filter(pred(x) => x >= 0i).front(); }', "1i");
        runMainCode('public function main(): Int { return List<Int>{1i, -1i}.filter(pred(x) => x >= 0i).back(); }', "1i");
    });
});

describe ("List -- filter index basic", () => {
    it("should do simple filter index", function () {
        runMainCode('public function main(): Nat { return List<Nat>{}.filterIdx(pred(x, i) => x >= i).size(); }', "0n");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.filterIdx(pred(x, i) => false).size(); }', "0n");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.filterIdx(pred(x, i) => true).size(); }', "3n");

        runMainCode('public function main(): Nat { return List<Nat>{1n}.filterIdx(pred(x, i) => x >= i).front(); }', "1n");
        runMainCode('public function main(): Nat { return List<Nat>{1n, 0n}.filterIdx(pred(x, i) => x >= i).back(); }', "1n");

        runMainCode('public function main(): Nat { return List<Nat>{0n, 1n, 2n}.filterIdx(pred(x, i) => x == i).size(); }', "3n");
        runMainCode('public function main(): Nat { return List<Nat>{0n, 1n, 2n}.filterIdx(pred(x, i) => x == i).back(); }', "2n");
    });
});
