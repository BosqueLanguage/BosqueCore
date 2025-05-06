"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- reduce simple", () => {
    it("should do simple bool reduce", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{}.reduce<Bool>(false, fn(acc, x) => acc && x > 0i); }', "false");

        runMainCode('public function main(): Bool { return List<Int>{1i, 3i}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{2i, 0i, 3i}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "false");
    });

    it("should do simple int reduce", function () {
        runMainCode('public function main(): Int { return List<Int>{}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "0i");
        runMainCode('public function main(): Int { return List<Int>{}.reduce<Int>(5i, fn(acc, x) => acc + x); }', "5i");

        runMainCode('public function main(): Int { return List<Int>{1i, 3i}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "4i");
        runMainCode('public function main(): Int { return List<Int>{-2i, 0i, 3i}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "1i");
    });

    it("should do simple int lreduce", function () {
        runMainCode('public function main(): Int { return List<Int>{}.lreduce<Int>(0i, fn(acc, x) => acc + x); }', "0i");
        runMainCode('public function main(): Int { return List<Int>{}.lreduce<Int>(5i, fn(acc, x) => acc + x); }', "5i");

        runMainCode('public function main(): Int { return List<Int>{1i, 3i}.lreduce<Int>(0i, fn(acc, x) => acc + x); }', "4i");
        runMainCode('public function main(): Int { return List<Int>{-2i, 0i, 3i}.lreduce<Int>(0i, fn(acc, x) => acc + x); }', "1i");
    });
});

describe ("List -- transduce simple", () => {
    it("should do simple int transduce", function () {
        runMainCode('public function main(): Int { return List<Int>{}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).0; }', "0i");
        runMainCode('public function main(): Nat { return List<Int>{}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.size(); }', "0n");

        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).0; }', "3i");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.size(); }', "3n");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.front(); }', "false");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.back(); }', "true");
    });

    it("should do simple int ltransduce", function () {
        runMainCode('public function main(): Int { return List<Int>{}.ltransduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).0; }', "0i");
        runMainCode('public function main(): Nat { return List<Int>{}.ltransduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.size(); }', "0n");

        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.ltransduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).0; }', "3i");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.ltransduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.size(); }', "3n");
    });
});

