"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit List -- access", () => {
    it("should get single", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.single(); }', "1_i"); 
    });

    it("should get back", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.back(); }', "1_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.back(); }', "2_i"); 
    });

    it("should get front", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.front(); }', "1_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.front(); }', "1_i"); 
    });

    it("should get index", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.get(0n); }', "1_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.get(0n); }', "1_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.get(1n); }', "2_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.get(1n); }', "2_i"); 
    });

    /*
    it("should fail get empty", function () {
        runMainCode('public function main(): Int { return List<Int>{}.back(); }', "(assert (not (is-@Result-err Main@main)))");
        runMainCode('public function main(): Int { return List<Int>{}.front(); }', "(assert (not (is-@Result-err Main@main)))");
        runMainCode('public function main(): Int { return List<Int>{}.get(0n); }', "(assert (not (is-@Result-err Main@main)))"); 
    });

    it("should fail get single", function () {
        runMainCode('public function main(): Int { return List<Int>{}.single(); }', "(assert (not (is-@Result-err Main@main)))");
        runMainCode('public function main(): Int { return List<Int>{0i, 5i}.single(); }', "(assert (not (is-@Result-err Main@main)))");
    });

    it("should fail get out-of-bounds", function () {
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.get(3n); }', "(assert (not (is-@Result-err Main@main)))");
    });
    */
});
