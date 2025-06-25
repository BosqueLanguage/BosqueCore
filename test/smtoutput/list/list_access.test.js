"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT List -- access", () => {
    it("smt should get single", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.single(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
    });

    it("smt should get back", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.back(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.back(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
    });

    it("smt should get front", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.front(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.front(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
    });

    it("smt should get index", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.get(0n); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i, 3i}.get(0n); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.get(1n); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i, 3i}.get(1n); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
    });

    it("smt should fail get empty", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.back(); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.front(); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.get(0n); }', "(assert (not (is-@Result-err Main@main)))"); 
    });

    it("smt should fail get single", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.single(); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{0i, 5i}.single(); }', "(assert (not (is-@Result-err Main@main)))");
    });

    it("smt should fail get out-of-bounds", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.get(3n); }', "(assert (not (is-@Result-err Main@main)))");
    });
});
