"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("CString -- startsString/endsString", () => {
    it("should startsString", function () {
        runMainCode("public function main(): Bool { return ''.startsWithString('ok'); }", [false, "Bool"]);

        runMainCode("public function main(): Bool { return 'ok'.startsWithString('x'); }", [false, "Bool"]); 
        runMainCode("public function main(): Bool { return 'a-ok'.startsWithString('a-'); }", [true, "Bool"]);  
    });

    it("should endsString", function () {
        runMainCode("public function main(): Bool { return ''.endsWithString('ok'); }", [false, "Bool"]);
        
        runMainCode("public function main(): Bool { return 'ok'.endsWithString('x'); }", [false, "Bool"]); 
        runMainCode("public function main(): Bool { return 'a-ok'.endsWithString('ok'); }", [true, "Bool"]);  
    });
});
