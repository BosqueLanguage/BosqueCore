"use strict";

import { sampledir, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

import { join } from "node:path";
import { readFileSync } from "node:fs";

const tttfilename = join(sampledir, "tic_tac_toe/tic_tac_toe.bsq");
console.log(`Running tictactoe test with dtype: ${tttfilename}`);
const dtype = "%%" + readFileSync(tttfilename, "utf8").toString();

describe ("tictactoe exec", () => {
    it("runit", function () {
        runTestSet(`${dtype}`, [['2n', 'false'], ['0n', 'true']], []);
    });
});
