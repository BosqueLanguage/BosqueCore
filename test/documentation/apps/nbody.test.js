"use strict";

import { sampledir, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

import { join } from "node:path";
import { readFileSync } from "node:fs";

const tttfilename = join(sampledir, "nbody/nbody.bsq");
const dtype = "%%" + readFileSync(tttfilename, "utf8").toString();

describe ("nbody exec", () => {
    it("runit", function () {
        runTestSet(`${dtype}`, [['0n', '-1.6907516382852444e-01f'], ['1n', '-1.6907495402506748e-01f'], ['3n', '-1.6907453142402259e-01f'], ['5000n', '-1.6902000037197423e-01f']], []);
    });
});
