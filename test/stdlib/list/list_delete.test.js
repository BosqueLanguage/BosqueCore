"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- delete", () => {
    it("should delete index", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.delete(1n).size(); }', "1n"); 
    });
    it("should delete to empty", function() {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.delete(1n).delete(0n).size(); }', "0n"); 
    });
    it("should fail invaid index", function() {
        runMainCodeError('public function main(): Nat { return List<Int>{1i, 2i}.delete(1n).delete(10n).size(); }', "Error -- i <= this.size() @ list.bsq"); 
    });
});
