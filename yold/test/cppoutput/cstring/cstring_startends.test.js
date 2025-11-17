"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate -- CString(rope) startsString/endsString", () => {
    it("should startsString", function () {
        runMainCode("public function main(): Bool { return ''.startsWithString('ok'); }", "false");

        runMainCode("public function main(): Bool { return 'ok'.startsWithString('x'); }", "false"); 
        runMainCode("public function main(): Bool { return 'a-ok'.startsWithString('a-'); }", "true");
    });
    it("should startsString on long-ish string", function () {
        runMainCode("public function main(): Bool { return 'Lorem ipsum dolor sit amet, consectetur adipiscing elit'.startsWithString('Lorem ipsum dolor sit amet, consectetur adipiscing elit'); }", "true");

        runMainCode("public function main(): Bool { return 'Lorem ipsum dolor sit amet, consectetur adipiscing elit'.startsWithString('Lorem ipsum dolor sit amet'); }", "true");
        runMainCode("public function main(): Bool { return 'Lorem ipsum dolor sit amet, consectetur adipiscing elit'.startsWithString('Lorem ipsum dolor sit amet, $'); }", "false");
    });

/*
    it("should endsString", function () {
        runMainCode("public function main(): Bool { return ''.endsWithString('ok'); }", "false");
        
        runMainCode("public function main(): Bool { return 'ok'.endsWithString('x'); }", "false"); 
        runMainCode("public function main(): Bool { return 'a-ok'.endsWithString('ok'); }", "true");  
    });
*/

});