"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate List -- set", () => {
    it("should set back", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.setBack(5i).size(); }', "2_n"); 

        runMainCode('public function main(): Int { return List<Int>{1i}.setBack(2i).back(); }', "2_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.setBack(5i).back(); }', "5_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.setBack(5i).front(); }', "1_i");
    });

    it("should set front", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.setFront(5i).size(); }', "2_n"); 

        runMainCode('public function main(): Int { return List<Int>{1i}.setFront(2i).front(); }', "2_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.setFront(5i).front(); }', "5_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.setFront(5i).back(); }', "2_i"); 
    });

    it("should set index", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i}.set(0n, 2i).size(); }', "1_n"); 

        runMainCode('public function main(): Int { return List<Int>{1i}.set(0n, 2i).get(0n); }', "2_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(0n, 5i).get(0n); }', "5_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.set(1n, 5i).get(1n); }', "5_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(1n, 5i).get(1n); }', "5_i");
        
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.set(1n, 5i).get(0n); }', "1_i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(1n, 5i).get(2n); }', "3_i");
    });

    /*
    it("should fail set empty smt", function () {
        runMainCode('public function main(): Int { return List<Int>{}.setBack(1i).get(0n); }', "(assert (not (is-@Result-err Main@main)))");
        runMainCode('public function main(): Int { return List<Int>{}.setFront(1i).get(0n); }', "(assert (not (is-@Result-err Main@main)))");
        runMainCode('public function main(): Int { return List<Int>{}.set(0n, 1i).get(0n); }', "(assert (not (is-@Result-err Main@main)))"); 
    });

    it("should fail set out-of-bounds smt", function () {
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.set(3n, 5i).get(1n); }', "(assert (not (is-@Result-err Main@main)))");
    });
    */
});
