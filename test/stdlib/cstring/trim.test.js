"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe("CString trim tests", () => {
    it("should trimFront", () => {
        runTestSet("public function main(s: CString): CString { return s.trimFront(); }", [['""', "''"], ['"   "', "''"], ['" abc"', "'abc'"], ['"abc "', "'abc '"], ['"   abc   "', "'abc   '"]], []);
    });

    it("should trimBack", () => {
        runTestSet("public function main(s: CString): CString { return s.trimBack(); }", [['""', "''"], ['"   "', "''"], ['"abc "', "'abc'"], ['" abc"', "' abc'"], ['"   abc   "', "'   abc'"]], []);
    });

        it("should trim", () => {
        runTestSet("public function main(s: CString): CString { return s.trim(); }", [['""', "''"], ['"   "', "''"], ['"abc"', "'abc'"], ['" abc"', "'abc'"], ['"abc "', "'abc'"], ['"   abc   "', "'abc'"]], []);
    });
});
