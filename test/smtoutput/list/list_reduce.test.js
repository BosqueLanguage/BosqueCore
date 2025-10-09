"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT List -- reduce simple", () => {
    it("should do simple bool reduce smt", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.reduce<Bool>(fn(acc, x) => acc && x > 0i, true); }', "(assert (not Main@main))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{}.reduce<Bool>(fn(acc, x) => acc && x > 0i, false); }', "(assert Main@main)");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 3i}.reduce<Bool>(fn(acc, x) => acc && x > 0i, true); }', "(assert (not Main@main))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{2i, 0i, 3i}.reduce<Bool>(fn(acc, x) => acc && x > 0i, true); }', "(assert Main@main)");
    });

    it("should do simple int reduce smt", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.reduce<Int>(fn(acc, x) => acc + x, 0i); }', "(assert (not (= 0 Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.reduce<Int>(fn(acc, x) => acc + x, 5i); }', "(assert (not (= 5 Main@main)))");

        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 3i}.reduce<Int>(fn(acc, x) => acc + x, 0i); }', "(assert (not (= 4 Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{-2i, 0i, 3i}.reduce<Int>(fn(acc, x) => acc + x, 0i); }', "(assert (not (= 1 Main@main)))");
    });

    it("should do simple int reduce smt w/err", function () {
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 3i}.reduce<Bool>(fn(acc, x) => { assert x != 0i; return acc && x > 0i; }, true); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 0i, 3i}.reduce<Bool>(fn(acc, x) => { assert x != 0i; return acc && x > 0i; }, true); }', "(assert (not (is-@Result-err Main@main)))");

        runishMainCodeUnsat('public function main(): Int { return List<Int>{-2i, 3i}.reduce<Int>(fn(acc, x) => { assert x != 0i; return acc + x; }, 0i); }', "(assert (not (= (@Result-ok 1) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{-2i, 0i, 3i}.reduce<Int>(fn(acc, x) => { assert x != 0i; return acc + x; }, 0i); }', "(assert (not (is-@Result-err Main@main)))");
    });

/*
    it("should do simple int lreduce smt", function () {
        runMainCode('public function main(): Int { return List<Int>{}.lreduce<Int>(0i, fn(acc, x) => acc + x); }', "0i");
        runMainCode('public function main(): Int { return List<Int>{}.lreduce<Int>(5i, fn(acc, x) => acc + x); }', "5i");

        runMainCode('public function main(): Int { return List<Int>{1i, 3i}.lreduce<Int>(0i, fn(acc, x) => acc + x); }', "4i");
        runMainCode('public function main(): Int { return List<Int>{-2i, 0i, 3i}.lreduce<Int>(0i, fn(acc, x) => acc + x); }', "1i");
    });
*/
});

/*
describe ("SMT List -- transduce simple", () => {
    it("should do simple int transduce smt", function () {
        runMainCode('public function main(): Int { return List<Int>{}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).0; }', "0i");
        runMainCode('public function main(): Nat { return List<Int>{}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.size(); }', "0n");

        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).0; }', "3i");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.size(); }', "3n");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.front(); }', "false");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.transduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.back(); }', "true");
    });

    it("should do simple int ltransduce smt", function () {
        runMainCode('public function main(): Int { return List<Int>{}.ltransduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).0; }', "0i");
        runMainCode('public function main(): Nat { return List<Int>{}.ltransduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.size(); }', "0n");

        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.ltransduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).0; }', "3i");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i, 3i}.ltransduce<Int, Bool>(0i, fn(e, x) => (|e + 1i, x > 2i|)).1.size(); }', "3n");
    });
});
*/
