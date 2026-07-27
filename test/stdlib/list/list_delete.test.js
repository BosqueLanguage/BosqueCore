"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it, run } from "node:test";

describe ("List -- delete", () => {
    it("should deleteFront basic", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.deleteFront(); }', [], ['0i']); 
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, z}.deleteFront(); }', [['2i', 'List<Int>{ 2i }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{z, 1i}.deleteFront().deleteFront(); }', [['2i', 'List<Int>{ }']], []);
    });

    it("should deleteBack basic", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.deleteBack(); }', [], ['0i']); 
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, z}.deleteBack(); }', [['2i', 'List<Int>{ 1i }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{z, 1i}.deleteBack().deleteBack(); }', [['2i', 'List<Int>{ }']], []);
    });

    it("should delete mixed", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{z, 3i, 1i}.deleteFront().deleteBack(); }', [['2i', 'List<Int>{ 3i }']], []);
    });

    it("should delete cycle", function () {
        runTestSet('public function main(z: Int): List<Int> { return List::rangeOfInt(3i, z).deleteBack().deleteBack().deleteBack().deleteBack().deleteBack().deleteBack().deleteBack().deleteBack(); }', [['22i', 'List<Int>{ 3i, 4i, 5i, 6i, 7i, 8i, 9i, 10i, 11i, 12i, 13i }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List::rangeOfInt(3i, z).deleteFront().deleteFront().deleteFront().deleteFront().deleteFront().deleteFront().deleteFront().deleteFront(); }', [['22i', 'List<Int>{ 11i, 12i, 13i, 14i, 15i, 16i, 17i, 18i, 19i, 20i, 21i }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List::rangeOfInt(3i, z).deleteFront().deleteBack().deleteFront().deleteBack().deleteFront().deleteBack().deleteFront().deleteBack(); }', [['22i', 'List<Int>{ 7i, 8i, 9i, 10i, 11i, 12i, 13i, 14i, 15i, 16i, 17i }']], []);
    });
});
