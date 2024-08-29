"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";


describe ("Checker -- String", () => {
    it("should check simple strings", function () {
        runMainCode('public function main(): String { return ""; }', ["", "String"]);
        runMainCode('public function main(): String { return "abc"; }', ["abc", "String"]);
        runMainCode('public function main(): String { return "a🌵c"; }', ["a🌵c", "String"]);
    });

    it("should check escaped strings", function () {
        runMainCode('public function main(): String { return "%x59;"; }', ["Y", "String"]);
        runMainCode('public function main(): String { return "%x1f335;"; }', ["🌵", "String"]);
        runMainCode('public function main(): String { return "%%;"; }', ["%", "String"]);
        runMainCode('public function main(): String { return "%;"; }', ["\"", "String"]);
    });
});

describe ("Checker -- CString", () => {
    it("should check simple cstrings", function () {
        runMainCode("public function main(): CString { return ''; }", ['', "CString"]);
        runMainCode("public function main(): CString { return 'abc'; }", ['abc', "CString"]);
        
    });

    it("should check escaped strings", function () {
        runMainCode("public function main(): CString { return '%x59;'; }", ['Y', "CString"]);
        runMainCode("public function main(): CString { return '%%;'; }", ['%', "CString"]);
        runMainCode("public function main(): CString { return '%;'; }", ['\'', "CString"]);
    });
});
