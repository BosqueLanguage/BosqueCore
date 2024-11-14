"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- construct empty and isEmpty", () => {
    it("should create simple list", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.empty(); }', [true, "Bool"]); 
        runMainCode('public function main(): Bool { return List<Int>{1i}.empty(); }', [false, "Bool"]); 
    });
});

describe ("List -- push back and size", () => {
    it("should create and size", function () {
        runMainCode('public function main(): Nat { return List<Int>{}.size(); }', [0n, "Nat"]); 
        runMainCode('public function main(): Nat { return List<Int>{1i}.size(); }', [1n, "Nat"]); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.size(); }', [3n, "Nat"]); 
    });
});

describe ("List -- access", () => {
    it("should get back", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.back(); }', [1n, "Int"]); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.back(); }', [2n, "Int"]); 
    });

    it("should get front", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.front(); }', [1n, "Int"]); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.front(); }', [1n, "Int"]); 
    });

    it("should get index", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.get(0n); }', [1n, "Int"]); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.get(0n); }', [1n, "Int"]); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.get(1n); }', [2n, "Int"]); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.get(1n); }', [2n, "Int"]); 
    });

    it("should fail empty", function () {
        runMainCodeError('public function main(): Int { return List<Int>{}.back(); }', "Error -- !ListOps::s_list_empty<T>(this) @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{}.front(); }', "Error -- !ListOps::s_list_empty<T>(this) @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{}.get(0n); }', "Error -- i < ListOps::s_list_size<T>(this) @ list.bsq"); 
    });

    it("should fail get out-of-bounds", function () {
        runMainCodeError('public function main(): Int { return List<Int>{1i, 2i}.get(3n); }', "Error -- i < ListOps::s_list_size<T>(this) @ list.bsq");
    });
});
