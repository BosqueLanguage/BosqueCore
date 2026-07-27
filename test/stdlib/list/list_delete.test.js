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
});
