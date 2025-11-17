"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("CString -- removePrefixString/removeSuffixString", () => {
    it("should removePrefixString", function () {
        runMainCode("public function main(): CString { return 'ok'.removePrefixString(''); }", "'ok'"); 
        runMainCode("public function main(): CString { return 'a-ok'.removePrefixString('a-'); }", "'ok'");  
    });

    it("should removeSuffixString", function () {
        runMainCode("public function main(): CString { return 'ok'.removeSuffixString(''); }", "'ok'"); 
        runMainCode("public function main(): CString { return 'a-ok'.removeSuffixString('ok'); }", "'a-'");  
    });

    it("should removeString error", function () {
        runMainCodeError("public function main(): CString { return 'ok'.removePrefixString('x'); }", "Error -- this.startsWithString(prefix) @ core.bsq"); 
        runMainCodeError("public function main(): CString { return 'ok'.removeSuffixString('x'); }", "Error -- this.endsWithString(suffix) @ core.bsq"); 
    });
});
