"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("CString -- append/prepend", () => {
    it("should append", function () {
        runMainCode("public function main(): CString { return ''.append('ok'); }", ["ok", "CString"]); 
        runMainCode("public function main(): CString { return 'ok'.append(''); }", ["ok", "CString"]); 

        runMainCode("public function main(): CString { return 'a-'.append('ok'); }", ["a-ok", "CString"]); 
    });

    it("should prepend", function () {
        runMainCode("public function main(): CString { return ''.prepend('ok'); }", ["ok", "CString"]); 
        runMainCode("public function main(): CString { return 'ok'.prepend(''); }", ["ok", "CString"]); 

        runMainCode("public function main(): CString { return 'ok'.prepend('a-'); }", ["a-ok", "CString"]); 
    });
});

describe ("CString -- concat", () => {
    it("should concat", function () {
        runMainCode("public function main(): CString { return CString::concat(); }", ["", "CString"]); 
        runMainCode("public function main(): CString { return CString::concat('a-', 'ok'); }", ["a-ok", "CString"]); 
        runMainCode("public function main(): CString { return CString::concat('a', '-', 'ok'); }", ["a-ok", "CString"]); 
    });

    it("should concatAll", function () {
        runMainCode("public function main(): CString { return CString::concatAll(List<CString>{}); }", ["", "CString"]); 
        runMainCode("public function main(): CString { return CString::concatAll(List<CString>{'a-', 'ok'}); }", ["a-ok", "CString"]); 
        runMainCode("public function main(): CString { return CString::concatAll(List<CString>{'a', '-', 'ok'}); }", ["a-ok", "CString"]); 
    });
});
