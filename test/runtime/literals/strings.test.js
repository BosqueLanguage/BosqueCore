"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Exec -- String", () => {
    it("should exec simple strings", function () {
        runMainCode('public function main(): String { return ""; }', '""');
        runMainCode('public function main(): String { return "abc"; }', '"abc"');
        runMainCode('public function main(): String { return "a🌵c"; }', '"a🌵c"');
    });

    it("should exec escaped strings", function () {
        runMainCode('public function main(): String { return "%x59;"; }', '"Y"');
        runMainCode('public function main(): String { return "%x1f335;"; }', '"🌵"');
        runMainCode('public function main(): String { return "%%;"; }', '"%%;"');
        runMainCode('public function main(): String { return "%;"; }', '"%;"');
    });
});

describe ("Exec -- CString", () => {
    it("should exec simple cstrings", function () {
        runMainCode("public function main(): CString { return ''; }", "''");
        runMainCode("public function main(): CString { return 'abc'; }", "'abc'");
        
    });

    it("should exec escaped strings", function () {
        runMainCode("public function main(): CString { return '%x59;'; }", "'Y'");
        runMainCode("public function main(): CString { return '%%;'; }", "'%$;'");
        runMainCode("public function main(): CString { return '%;'; }", "'%;'");
    });
});
