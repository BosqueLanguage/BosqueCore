"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("Algos -- while basic", () => {
    it("should do while", function () {
        runMainCode('public function main() : Int { return Algorithm::while<Int>(0i, pred(x) => x < 10i, fn(x) => x + 1i);}', "10_i");
    });
});