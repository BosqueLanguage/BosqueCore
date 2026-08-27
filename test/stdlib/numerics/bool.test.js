"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Bool Operations", () => {
    it("should compute tostring", function () {
        runTestSet('public function main(b: Bool): CString { return Bool::toCString(b); }', [['true', "'true'"], ['false', "'false'"]], []);

        runTestSet('public function main(b: Bool): String { return Bool::toString(b); }', [['true', '"true"'], ['false', '"false"']], []);
    });
});
