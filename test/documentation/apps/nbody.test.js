"use strict";

import { sampledir, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

import { join } from "node:path";
import { readFileSync } from "node:fs";

const tttfilename = join(sampledir, "nbody/nbody.bsq");
const dtype = "%%" + readFileSync(tttfilename, "utf8").toString();

describe ("nbody exec", () => {
    it("runit", function () {
        runTestSet(`${dtype}`, [['0n', '-0.169075163829f'], ['1n', '-0.169074954025f'], ['3n', '-0.169074531424f']], []);
    });
});
