"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("CString -- append/prepend", () => {
    it("should append", function () {
        runMainCode("public function main(): CString { return ''.append('ok'); }", "'ok'"); 
        runMainCode("public function main(): CString { return 'ok'.append(''); }", "'ok'"); 

        runMainCode("public function main(): CString { return 'a-'.append('ok'); }", "'a-ok'"); 
    });

    it("should prepend", function () {
        runMainCode("public function main(): CString { return ''.prepend('ok'); }", "'ok'"); 
        runMainCode("public function main(): CString { return 'ok'.prepend(''); }", "'ok'"); 

        runMainCode("public function main(): CString { return 'ok'.prepend('a-'); }", "'a-ok'"); 
    });
});

describe ("CString -- concat", () => {
    it("should concat", function () {
        runMainCode("public function main(): CString { return CString::concat(); }", "''"); 
        runMainCode("public function main(): CString { return CString::concat('a-', 'ok'); }", "'a-ok'"); 
        runMainCode("public function main(): CString { return CString::concat('a', '-', 'ok'); }", "'a-ok'"); 
    });

    it("should concatAll", function () {
        runMainCode("public function main(): CString { return CString::concatAll(List<CString>{}); }", "''"); 
        runMainCode("public function main(): CString { return CString::concatAll(List<CString>{'a-', 'ok'}); }", "'a-ok'"); 
        runMainCode("public function main(): CString { return CString::concatAll(List<CString>{'a', '-', 'ok'}); }", "'a-ok'"); 
    });
});

describe ("CString -- join", () => {
    it("should join", function () {
        runMainCode("public function main(): CString { return CString::join('-'); }", "''"); 
        runMainCode("public function main(): CString { return CString::join('-', '1'); }", "'1'"); 
        runMainCode("public function main(): CString { return CString::join('-', '1', '2'); }", "'1-2'"); 
        runMainCode("public function main(): CString { return CString::join('-', '1', '2', '3'); }", "'1-2-3'"); 
    });

    it("should joinAll", function () {
        runMainCode("public function main(): CString { return CString::joinAll('-', List<CString>{}); }", "''"); 
        runMainCode("public function main(): CString { return CString::joinAll('-', List<CString>{'1'}); }", "'1'"); 
        runMainCode("public function main(): CString { return CString::joinAll('-', List<CString>{'1', '2'}); }", "'1-2'"); 
        runMainCode("public function main(): CString { return CString::joinAll('-', List<CString>{'1', '2', '3'}); }", "'1-2-3'"); 
    });
});
