"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Algos -- worklist basic", () => {
    it("should do worklist", function () {
        runMainCode('public function main() : Int { return Algorithm::worklist<Int, Int>(0i, List<Int>{0i}, fn(s, v) => { if (v <= 10i) { let n = v + 1i; return (|s + v, List<Int>{n}|); } else { return (|s, List<Int>{}|); } }); }', "55i");
    });
});

