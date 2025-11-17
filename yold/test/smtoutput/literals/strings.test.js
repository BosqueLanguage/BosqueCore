"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- CString", () => {
    it("should smt exec cregex", function () {
        runishMainCodeUnsat("public function main(): CString { return ''; }", '(assert (not (= Main@main "")))');
        runishMainCodeUnsat("public function main(): CString { return 'abc'; }", '(assert (not (= Main@main "abc")))');
    });
});

describe ("SMT -- String", () => {
    it("should smt exec simple string", function () {
        runishMainCodeUnsat('public function main(): String { return ""; }', '(assert (not (= Main@main "")))');
        runishMainCodeUnsat('public function main(): String { return "abc"; }', '(assert (not (= Main@main "abc")))');

    });
});
