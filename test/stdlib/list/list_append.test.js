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

    it("should concat/flatten", function () {
        runTestSet('public function main(l: List<Int>): List<Int> { let lpre = List<Int>{ 1i, 2i, 3i }; let lpost = List<Int>{ 10i, 11i, 12i }; return List<Int>::concat(l, lpre, l, lpost); }', [['List<Int>{}', 'List<Int>{ 1i, 2i, 3i, 10i, 11i, 12i }'],['List<Int>{ 4i, 5i }', 'List<Int>{ 4i, 5i, 1i, 2i, 3i, 4i, 5i, 10i, 11i, 12i }']], []);
        runTestSet('public function main(l: List<Int>): List<Int> { let lpre = List<Int>{ 1i, 2i, 3i }; let lpost = List<Int>{ 10i, 11i, 12i }; return List<Int>::concatAll(List<List<Int>>{l, lpre, l, lpost}); }', [['List<Int>{}', 'List<Int>{ 1i, 2i, 3i, 10i, 11i, 12i }'],['List<Int>{ 4i, 5i }', 'List<Int>{ 4i, 5i, 1i, 2i, 3i, 4i, 5i, 10i, 11i, 12i }']], []);
        runTestSet('public function main(l: List<Int>): List<Int> { let lpre = List<Int>{ 1i, 2i, 3i }; let lpost = List<Int>{ 10i, 11i, 12i }; return List<List<Int>>{l, lpre, l, lpost}.flatten<Int>(); }', [['List<Int>{}', 'List<Int>{ 1i, 2i, 3i, 10i, 11i, 12i }'],['List<Int>{ 4i, 5i }', 'List<Int>{ 4i, 5i, 1i, 2i, 3i, 4i, 5i, 10i, 11i, 12i }']], []);

        runTestSet("public function main(l: List<CString>): List<CString> { let lpre = List<CString>{ 'a', 'b', 'c' }; let lpost = List<CString>{ 'x', 'y' }; return List<CString>::concat(l, lpre, l, lpost); }", [['List<CString>{}', "List<CString>{ 'a', 'b', 'c', 'x', 'y' }"], ['List<CString>{"q"}', "List<CString>{ 'q', 'a', 'b', 'c', 'q', 'x', 'y' }"]], []);
    });
});

