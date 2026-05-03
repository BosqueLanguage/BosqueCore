"use strict";

import { runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const allpositive = 'function allPositive(...args: List<Int>): Bool { return args.allOf(pred(x) => x >= 0i); }';

describe ("allof exec", () => {
    it("should exec allof", function () {
        runTestSet(`${allpositive} public function main(x: Int): Bool { return allPositive(); }`, [['3i', 'true']], []);
        runTestSet(`${allpositive} public function main(x: Int): Bool { return allPositive(1i, x, 4i); }`, [['3i', 'true'], ['-3i', 'false']], []);
    });
});
