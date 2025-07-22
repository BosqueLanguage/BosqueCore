"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- delete", () => {
    it("should delete index", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.delete(1n).size(); }', "1n");
        runMainCode('public function main(): Int { return List<Int>{1i, 3i}.pushBack(2i).delete(1n).back(); }', "2i"); 
        runMainCode('public function main(): Int { return List<Int>{2i, 2i}.pushFront(3i).delete(2n).front(); }', "3i"); 
        runMainCode('public function main(): Nat { return List<Int>{2i, 2i}.pushFront(3i).delete(2n).size(); }', "2n"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.pushBack(3i).pushBack(4i).delete(1n).get(2n); }', "4i"); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.pushBack(3i).pushBack(4i).pushBack(5i).delete(0n).delete(0n).size(); }', "3n"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.pushBack(3i).pushBack(4i).pushBack(5i).pushBack(6i).delete(0n).delete(0n).get(0n); }', "3i"); 
        runMainCode('public function main(): Nat { return List<Int>{4i, 5i}.pushFront(3i).pushFront(2i).pushFront(1i).pushBack(6i).pushBack(7i).delete(0n).delete(0n).delete(3n).size(); }', "4n"); 
        runMainCode('public function main(): Int { return List<Int>{1i}.pushBack(2i).pushFront(3i).delete(0n).front(); }', "1i"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.delete(1n).get(0n); }', "1i"); 
    });
    
    it("should delete front", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.deleteFront().size(); }', "1n");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.pushFront(3i).deleteFront().front(); }', "1i"); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.pushFront(3i).pushBack(0i).deleteFront().deleteFront().deleteFront().deleteFront().size(); }', "0n"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.insert(2n, 3i).deleteFront().get(1n); }', "3i"); 
    });
    
    it("should fail delete front if empty", function () {
        runMainCodeError('public function main(): Nat { return List<Int>{1i, 2i}.deleteFront().deleteFront().deleteFront().size(); }', "Error -- !this.empty() @ list.bsq");
    });
    
    it("should delete back", function () {
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.deleteBack().size(); }', "1n");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.pushBack(3i).deleteBack().back(); }', "2i"); 
        runMainCode('public function main(): Nat { return List<Int>{1i, 2i}.pushBack(3i).pushBack(0i).deleteBack().deleteBack().deleteBack().deleteBack().size(); }', "0n"); 
        runMainCode('public function main(): Int { return List<Int>{1i, 2i}.insert(2n, 3i).deleteBack().deleteBack().get(0n); }', "1i"); 
    });
    
    it("should fail delete back if empty", function () {
        runMainCodeError('public function main(): Nat { return List<Int>{1i, 2i}.deleteBack().deleteBack().deleteBack().size(); }', "Error -- !this.empty() @ list.bsq");
    });
    
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
});
