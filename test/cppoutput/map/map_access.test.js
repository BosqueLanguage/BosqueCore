"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- Map access", () => {
    it("should get single", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.single().value; }', "2_i"); 
    });

    it("should get max", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.kmax().value; }', "2_i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.kmax().value; }', "3_i"); 
    });

    it("should get min", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.kmin().value; }', "2_i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.kmin().value; }', "2_i"); 
    });

    it("should get key", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.get(1i); }', "2_i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.get(1i); }', "2_i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.get(2i); }', "3_i"); 
    });

    it("should tryGet key", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.tryGet(1i)@some; }', "2_i"); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.tryGet(1i)@some; }', "2_i"); 

        runMainCode('public function main(): Bool { return Map<Int, Int>{1i => 2i, 2i => 3i}.tryGet(5i)?none; }', "true"); 
    });

    // CPP Emitter is lacking pre and post conds so this does not work!
/*
    it("should fail get empty", function () {
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.kmin().value; }', "Assertion failed! Or perhaps over/underflow?\n");
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.kmax().value; }', "Assertion failed! Or perhaps over/underflow?\n");
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.get(0i); }', "Assertion failed! Or perhaps over/underflow?\n"); 
    });
    
    it("should fail get single", function () {
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.single().value; }', "Assertion failed! Or perhaps over/underflow?\n");
        runMainCodeError('public function main(): Int { return Map<Int, Int>{0i => 5i, 2i => 4i}.single().value; }', "Assertion failed! Or perhaps over/underflow?\n");
    });
*/

    it("should fail get missing", function () {
        runMainCodeError('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.get(3i); }', "Assertion failed! Or perhaps over/underflow?\n");
    });
});
