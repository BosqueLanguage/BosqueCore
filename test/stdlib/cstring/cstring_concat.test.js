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

describe ("CString -- join", () => {
    it("should join", function () {
        runMainCode("public function main(): CString { return CString::join('-'); }", ["", "CString"]); 
        runMainCode("public function main(): CString { return CString::join('-', '1'); }", ["1", "CString"]); 
        runMainCode("public function main(): CString { return CString::join('-', '1', '2'); }", ["1-2", "CString"]); 
        runMainCode("public function main(): CString { return CString::join('-', '1', '2', '3'); }", ["1-2-3", "CString"]); 
    });

    it("should joinAll", function () {
        runMainCode("public function main(): CString { return CString::joinAll('-', List<CString>{}); }", ["", "CString"]); 
        runMainCode("public function main(): CString { return CString::joinAll('-', List<CString>{'1'}); }", ["1", "CString"]); 
        runMainCode("public function main(): CString { return CString::joinAll('-', List<CString>{'1', '2'}); }", ["1-2", "CString"]); 
        runMainCode("public function main(): CString { return CString::joinAll('-', List<CString>{'1', '2', '3'}); }", ["1-2-3", "CString"]); 
    });
});
