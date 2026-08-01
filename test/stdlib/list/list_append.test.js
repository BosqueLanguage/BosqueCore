"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- append", () => {
    it("should append", function () {
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{}.append(List<Int>{z}); }', [['1i', 'List<Int>{ 1i }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{z}.append(List<Int>{}); }', [['1i', 'List<Int>{ 1i }']], []);

        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, 2i, 3i}.append(List<Int>{z, 4i}); }', [['1i', 'List<Int>{ 1i, 2i, 3i, 1i, 4i }']], []);

        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, 2i, 3i}.append(List<Int>{z, 4i}).prepend(List<Int>{ 10i, 11i, 12i }); }', [['1i', 'List<Int>{ 10i, 11i, 12i, 1i, 2i, 3i, 1i, 4i }']], []);
        runTestSet('public function main(z: Int): List<Int> { return List<Int>{1i, 2i, 3i}.prepend(List<Int>{z, 4i}).append(List<Int>{ 10i, 11i, 12i }); }', [['1i', 'List<Int>{ 1i, 4i, 1i, 2i, 3i, 10i, 11i, 12i }']], []);
    });
});

