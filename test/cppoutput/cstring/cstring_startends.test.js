"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CString -- startsString/endsString", () => {
    it("should startsString", function () {
        runMainCode("public function main(): Bool { return ''.startsWithString('ok'); }", "false");

        runMainCode("public function main(): Bool { return 'ok'.startsWithString('x'); }", "false"); 
        runMainCode("public function main(): Bool { return 'a-ok'.startsWithString('a-'); }", "true");  
    });

/*
    it("should endsString", function () {
        runMainCode("public function main(): Bool { return ''.endsWithString('ok'); }", "false");
        
        runMainCode("public function main(): Bool { return 'ok'.endsWithString('x'); }", "false"); 
        runMainCode("public function main(): Bool { return 'a-ok'.endsWithString('ok'); }", "true");  
    });
*/

});