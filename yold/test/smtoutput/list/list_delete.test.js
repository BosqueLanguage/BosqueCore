"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT List -- delete", () => {
    it("should delete index", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.delete(1n).size(); }', "(assert (not (= (@Result-ok 1) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 3i}.pushBack(2i).delete(1n).back(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{2i, 2i}.pushFront(3i).delete(2n).front(); }', "(assert (not (= (@Result-ok 3) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{2i, 2i}.pushFront(3i).delete(2n).size(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i}.pushBack(2i).pushFront(3i).delete(0n).front(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.delete(1n).get(0n); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
    });
    
    it("should delete front", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.deleteFront().size(); }', "(assert (not (= (@Result-ok 1) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.pushFront(3i).deleteFront().front(); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.pushFront(3i).deleteFront().get(1n); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
    });
    
    it("should fail delete front if empty", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.deleteFront().deleteFront().deleteFront().size(); }', "(assert (not (is-@Result-err Main@main)))");
    });
    
    it("should delete back", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.deleteBack().size(); }', "(assert (not (= (@Result-ok 1) Main@main)))");
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.pushBack(3i).deleteBack().back(); }', "(assert (not (= (@Result-ok 2) Main@main)))"); 
        runishMainCodeUnsat('public function main(): Int { return List<Int>{1i, 2i}.pushBack(3i).deleteBack().deleteBack().get(0n); }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
    });
    
    it("should fail delete back if empty", function () {
        runishMainCodeUnsat('public function main(): Nat { return List<Int>{1i, 2i}.deleteBack().deleteBack().deleteBack().size(); }', "(assert (not (is-@Result-err Main@main)))");
    });
    /*
    it("should pop front", function () {
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.popFront().0; }', "1i");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.popFront().1.size(); }', "1n");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.pushFront(3i).popFront().0; }', "3i");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.pushFront(3i).popFront().1.size(); }', "2n");
    });
    
    it("should fail pop front if empty", function () {
        runMainCodeError('public function main(): Int { return List<Int>{1i}.popFront().1.popFront().0; }', "Error -- !this.empty() @ list.bsq");
    });

    it("should pop back", function () {
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.popBack().0; }', "2i");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.popBack().1.size(); }', "1n");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.pushBack(3i).popBack().0; }', "3i");
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.pushBack(3i).popBack().1.size(); }', "2n");
    });

    it("should fail pop back if empty", function () {
        runMainCodeError('public function main(): Int { return List<Int>{1i}.popBack().1.popBack().0; }', "Error -- !this.empty() @ list.bsq");
    });

    it("should delete to empty", function() {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.delete(1n).delete(0n).size(); }', "0n"); 
        runMainCode('public function main(): Bool { return List<Int>{1i, 4i}.delete(0n).delete(0n).empty(); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{1i, 3i}.pushBack(0i).pushFront(9i).pushBack(6i).delete(0n).delete(0n).delete(0n).delete(0n).delete(0n).empty(); }', "true");
    });

    it("should fail invaid index", function() {
        runMainCodeError('public function main(): Nat { return List<Int>{1i, 2i}.delete(1n).delete(10n).size(); }', "Error -- i < this.size() @ list.bsq"); 
        runMainCodeError('public function main(): Nat { return List<Int>{1i, 3i}.pushBack(2i).delete(4n).size(); }', "Error -- i < this.size() @ list.bsq"); 
    });
    */
});
