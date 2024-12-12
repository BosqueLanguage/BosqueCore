"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("CString -- empty", () => {
    it("should create simple list", function () {
        runMainCode("public function main(): CString { return ''; }", ["", "CString"]); 
        runMainCode("public function main(): Bool { return ''.empty(); }", [true, "Bool"]); 
        runMainCode("public function main(): Bool { return 'ok'.empty(); }", [false, "Bool"]); 
    });
});

