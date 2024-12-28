"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Map -- access", () => {
    it("should get single", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.single().value; }', [2n, "Int"]); 
    });

    it("should get max", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.kmax().value; }', [2n, "Int"]); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.kmax().value; }', [3n, "Int"]); 
    });

    it("should get min", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.kmin().value; }', [2n, "Int"]); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.kmin().value; }', [2n, "Int"]); 
    });

    it("should get key", function () {
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i}.get(1i); }', [2n, "Int"]); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.get(1i); }', [2n, "Int"]); 
        runMainCode('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.get(2i); }', [3n, "Int"]); 
    });

    it("should fail get empty", function () {
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.kmin().value; }', "Error -- !this.empty() @ map.bsq");
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.kmax().value; }', "Error -- !this.empty() @ map.bsq");
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.get(0i); }', "Error -- this.has(k) @ map.bsq"); 
    });

    it("should fail get single", function () {
        runMainCodeError('public function main(): Int { return Map<Int, Int>{}.single().value; }', "Error -- this.isSingleElement() @ map.bsq");
        runMainCodeError('public function main(): Int { return Map<Int, Int>{0i => 5i, 2i => 4i}.single().value; }', "Error -- this.isSingleElement() @ map.bsq");
    });

    it("should fail get missing", function () {
        runMainCodeError('public function main(): Int { return Map<Int, Int>{1i => 2i, 2i => 3i}.get(3i); }', "Error -- this.has(k) @ map.bsq");
    });
});
