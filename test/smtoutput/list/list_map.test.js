"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT List -- map basic", () => {
    it("should do simple maps", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{}.map<Bool>(fn(x) => x >= 0i).size(); }', "(assert (not (= 0 Main@main)))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i}.map<Bool>(fn(x) => x >= 0i).front(); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, -1i}.map<Bool>(fn(x) => x >= 0i).back(); }', "(assert (not (= (@Result-ok false) Main@main)))");
    });

    it("should do simple maps w/err", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{}.map<Bool>(fn(x) => { assert x != 0i; return x >= 0i; }).size(); }', "(assert (not (= (@Result-ok 0) Main@main)))");

        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i}.map<Bool>(fn(x) => { assert x != 0i; return x >= 0i; }).front(); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runishMainCodeUnsat('public function main(): Bool { return List<Int>{1i, 0i, -1i}.map<Bool>(fn(x) => { assert x != 0i; return x >= 0i; }).back(); }', "(assert (not (is-@Result-err Main@main)))");
    });
});
/*
describe ("SMT List -- map index basic", () => {
    it("should do simple maps index", function () {
        runMainCode('public function main(): Nat { return List<Nat>{}.mapIdx<Bool>(fn(x, i) => x >= i).size(); }', "0n");

        runMainCode('public function main(): Bool { return List<Nat>{1n}.mapIdx<Bool>(fn(x, i) => x >= i).front(); }', "true");
        runMainCode('public function main(): Bool { return List<Nat>{1n, 0n}.mapIdx<Bool>(fn(x, i) => x >= i).back(); }', "false");

        runMainCode('public function main(): Nat { return List<Int>{1i, -1i, 3i}.mapIdx<Nat>(fn(x, i) => i).back(); }', "2n");
    });
});
*/