import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- set", () => {
    it("should set back", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.setBack(5i).size(); }', "2n"); 

        runMainCode('public function main(): Int { return List<Int>{1i}.setBack(2i).back(); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.setBack(5i).back(); }', "5i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.setBack(5i).front(); }', "1i"); 
    });

    it("should set front", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.setFront(5i).size(); }', "2n"); 

        runMainCode('public function main(): Int { return List<Int>{1i}.setFront(2i).front(); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.setFront(5i).front(); }', "5i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.setFront(5i).back(); }', "2i"); 
    });

    it("should set index", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i}.set(0n, 2i).size(); }', "1n"); 

        runMainCode('public function main(): Int { return List<Int>{1i}.set(0n, 2i).get(0n); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(0n, 5i).get(0n); }', "5i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.set(1n, 5i).get(1n); }', "5i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(1n, 5i).get(1n); }', "5i");
        
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.set(1n, 5i).get(0n); }', "1i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(1n, 5i).get(2n); }', "3i");
    });

    it("should fail set empty", function () {
        runMainCodeError('public function main(): Int { return List<Int>{}.setBack(1i).get(0n); }', "Error -- !this.empty() @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{}.setFront(1i).get(0n); }', "Error -- !this.empty() @ list.bsq");
        runMainCodeError('public function main(): Int { return List<Int>{}.set(0n, 1i).get(0n); }', "Error -- i < this.size() @ list.bsq"); 
    });

    it("should fail set out-of-bounds", function () {
        runMainCodeError('public function main(): Int { return List<Int>{1i, 2i}.set(3n, 5i).get(1n); }', "Error -- i < this.size() @ list.bsq");
    });
});
