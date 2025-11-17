"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- CString", () => {
    it("should smt exec cregex accepts", function () {
        runishMainCodeUnsat("public function main(s: CString): Bool { return CRegex::accepts(/'x'[0-9]{1,4}/c, s); }", '(assert (not (Main@main "x3")))');
        runishMainCodeUnsat("public function main(s: CString): Bool { return CRegex::accepts(/'x'[0-9]{1,4}/c, s); }", '(assert (Main@main "okay"))');

        runishMainCodeUnsat("public function main(s: CString): Bool { return CRegex::accepts(/'yes' | 'no'/c, s); }", '(assert (not (Main@main "yes")))');
        runishMainCodeUnsat("public function main(s: CString): Bool { return CRegex::accepts(/'yes' | 'no'/c, s); }", '(assert (not (Main@main "no")))');
        runishMainCodeUnsat("public function main(s: CString): Bool { return CRegex::accepts(/'yes' | 'no'/c, s); }", '(assert (Main@main "maybe"))');
    });
});

describe ("SMT -- String", () => {
    it("should smt exec simple regex accepts", function () {
        runishMainCodeUnsat('public function main(s: String): Bool { return Regex::accepts(/"x"[0-9]{1,4}/, s); }', '(assert (not (Main@main "x3")))');
        runishMainCodeUnsat('public function main(s: String): Bool { return Regex::accepts(/"x"[0-9]{1,4}/, s); }', '(assert (Main@main "okay"))');

        runishMainCodeUnsat('public function main(s: String): Bool { return Regex::accepts(/"yes" | "no"/, s); }', '(assert (not (Main@main "yes")))');
        runishMainCodeUnsat('public function main(s: String): Bool { return Regex::accepts(/"yes" | "no"/, s); }', '(assert (not (Main@main "no")))');
        runishMainCodeUnsat('public function main(s: String): Bool { return Regex::accepts(/"yes" | "no"/, s); }', '(assert (Main@main "maybe"))');
    });
});

