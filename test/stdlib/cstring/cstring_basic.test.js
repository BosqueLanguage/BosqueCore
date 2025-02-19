"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("CString -- empty", () => {
    it("should create simple cstring", function () {
        runMainCode("public function main(): CString { return ''; }", "''"); 
        runMainCode("public function main(): Bool { return ''.empty(); }", "true"); 
        runMainCode("public function main(): Bool { return 'ok'.empty(); }", "false"); 
    });

    it("should do sizes cstring", function () {
        runMainCode("public function main(): Nat { return ''.size(); }", "0n"); 
        runMainCode("public function main(): Nat { return 'abc'.size(); }", "3n"); 
        runMainCode("public function main(): Nat { return 'ok'.lastIndex(); }", "1n"); 
    });
});

