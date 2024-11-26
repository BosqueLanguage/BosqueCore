"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- map basic", () => {
    it("should do simple maps", function () {
        runMainCode('public function main(): Nat { return List<Int>{}.map<Bool>(fn(x) => x >= 0i).size(); }', [0n, "Nat"]);

        runMainCode('public function main(): Bool { return List<Int>{1i}.map<Bool>(fn(x) => x >= 0i).front(); }', [true, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{1i, -1i}.map<Bool>(fn(x) => x >= 0i).back(); }', [false, "Bool"]);
    });
});

describe ("List -- map index basic", () => {
    it("should do simple maps index", function () {
        runMainCode('public function main(): Nat { return List<Nat>{}.mapIdx<Bool>(fn(x, i) => x >= i).size(); }', [0n, "Nat"]);

        runMainCode('public function main(): Bool { return List<Nat>{1n}.mapIdx<Bool>(fn(x, i) => x >= i).front(); }', [true, "Bool"]);
        runMainCode('public function main(): Bool { return List<Nat>{1n, 0n}.mapIdx<Bool>(fn(x, i) => x >= i).back(); }', [false, "Bool"]);

        runMainCode('public function main(): Nat { return List<Int>{1i, -1i, 3i}.mapIdx<Nat>(fn(x, i) => i).back(); }', [2n, "Nat"]);
    });
});
