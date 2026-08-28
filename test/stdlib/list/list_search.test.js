"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- contains basic", () => {
    it("should do simple contains", function () {
        runTestSet('public function main(l: List<Int>): Bool { return l.contains(0i); }', [['List<Int>{}', 'false'], ['List<Int>{0i}', 'true'], ['List<Int>{1i}', 'false'], ['List<Int>{1i, 2i, 3i, 4i, 5i, 6i, 7i, 0i, 8i}', 'true'], ['List<Int>{1i, 2i, 3i, 4i, 5i, 6i, 7i, 8i}', 'false']], []);
    });

    it("should do finds", function () {
        runTestSet('public function main(l: List<Int>): Int { return l.find(pred(v) => v > 3i); }', [['List<Int>{4i}', '4i'], ['List<Int>{1i, 2i, 3i, 4i, 5i, 6i, 7i, 0i, 8i}', '4i'], ['List<Int>{1i, 2i, 1i, 2i, 1i, 6i, 2i, 8i}', '6i']], ['List<Int>{}', 'List<Int>{1i}']);

        runTestSet('public function main(l: List<Int>): Option<Int> { return l.findTry(pred(v) => v > 3i); }', [['List<Int>{}', 'none'], ['List<Int>{1i}', 'none'], ['List<Int>{4i}', 'some(4i)'], ['List<Int>{1i, 2i, 3i, 4i, 5i, 6i, 7i, 0i, 8i}', 'some(4i)'], ['List<Int>{1i, 2i, 1i, 2i, 1i, 6i, 2i, 8i}', 'some(6i)'], ['List<Int>{1i, 2i, 1i, 2i, 1i, 1i, 2i, 1i}', 'none']], []);
        runTestSet('public function main(l: List<Int>): Int { var v: Int; if(l.findCond(out? v, pred(v) => v > 3i)) { return v; } else { return -1i; } }', [['List<Int>{}', '-1i'], ['List<Int>{1i}', '-1i'], ['List<Int>{4i}', '4i'], ['List<Int>{1i, 2i, 3i, 4i, 5i, 6i, 7i, 0i, 8i}', '4i'], ['List<Int>{1i, 2i, 1i, 2i, 1i, 6i, 2i, 8i}', '6i'], ['List<Int>{1i, 2i, 1i, 2i, 1i, 1i, 2i, 1i}', '-1i']], []);
    });
});
