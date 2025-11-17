
import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT List -- set", () => {
    it("should set back smt", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.setBack(5i).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 

        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.setBack(2i).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.setBack(5i).back(); }', "(assert (not (= (@Result-ok 5) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.setBack(5i).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))");
    });

    it("should set front smt", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.setFront(5i).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 

        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.setFront(2i).front(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.setFront(5i).front(); }', "(assert (not (= (@Result-ok 5) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.setFront(5i).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
    });

    it("should set index smt", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i}.set(0n, 2i).size(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 

        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.set(0n, 2i).get(0n); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(0n, 5i).get(0n); }', "(assert (not (= (@Result-ok 5) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.set(1n, 5i).get(1n); }', "(assert (not (= (@Result-ok 5) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(1n, 5i).get(1n); }', "(assert (not (= (@Result-ok 5) Main@main)))");
        
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.set(1n, 5i).get(0n); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i, 3i}.set(1n, 5i).get(2n); }', "(assert (not (= (@Result-ok 3) Main@main)))");
    });

    it("should fail set empty smt", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.setBack(1i).get(0n); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.setFront(1i).get(0n); }', "(assert (not (is-@Result-err Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{}.set(0n, 1i).get(0n); }', "(assert (not (is-@Result-err Main@main)))"); 
    });

    it("should fail set out-of-bounds smt", function () {
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.set(3n, 5i).get(1n); }', "(assert (not (is-@Result-err Main@main)))");
    });
});
