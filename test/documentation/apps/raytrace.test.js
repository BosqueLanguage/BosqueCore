"use strict";

import { sampledir, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

import { join } from "node:path";
import { readFileSync } from "node:fs";

const tttfilename = join(sampledir, "raytrace/raytrace.bsq");
const dtype = "%%" + readFileSync(tttfilename, "utf8").toString();

describe ("raytrace exec", () => {
    it("runit", function () {
        runTestSet(`${dtype}`, [['10n', '']], []);
        runTestSet(`${dtype}`, [['100n', '']], []);
    });
});
