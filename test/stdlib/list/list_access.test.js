import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- access", () => {
    it("should get single", function () {
        runMainCode('public function main(): Int { return List<Int>{1i}.single(); }', [1n, "Int"]); 
    });

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

    it("should fail get empty", function () {
        runMainCodeError('public function main(): Int { return List<Int>{}.back(); }', "Error -- !this.empty() @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{}.front(); }', "Error -- !this.empty() @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{}.get(0n); }', "Error -- i < this.size() @ list.bsq"); 
    });

    it("should fail get single", function () {
        runMainCodeError('public function main(): Int { return List<Int>{}.single(); }', "Error -- this.isSingleElement() @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{0i, 5i}.single(); }', "Error -- this.isSingleElement() @ list.bsq");
    });

    it("should fail get out-of-bounds", function () {
        runMainCodeError('public function main(): Int { return List<Int>{1i, 2i}.get(3n); }', "Error -- i < this.size() @ list.bsq");
    });
});
