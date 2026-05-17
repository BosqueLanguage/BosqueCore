"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- String", () => {
    it("should emit simple strings", function () {
        checkTestEmitMainFunction('public function main(): String { return ""; }', 'String Mainᕒmain() { return U""_us; }');
        checkTestEmitMainFunction('public function main(): String { return "abc"; }', 'String Mainᕒmain() { return U"abc"_us; }');
        //checkTestEmitMainFunction('public function main(): String { return "a🌵c"; }', 'String Mainᕒmain() { return U"a🌵c"_us; }');
    });

    it("should emit escaped strings", function () {
        checkTestEmitMainFunction('public function main(): String { return "%x59;"; }', 'String Mainᕒmain() { return U"Y"_us; }');
        //checkTestEmitMainFunction('public function main(): String { return "%x1f335;"; }', 'String Mainᕒmain() { return U"🌵"_us; }');
        checkTestEmitMainFunction('public function main(): String { return "%%;"; }', 'String Mainᕒmain() { return U"%"_us; }');
        checkTestEmitMainFunction('public function main(): String { return "%;"; }', 'String Mainᕒmain() { return U"\\""_us; }');
    });
});

describe ("CPPEmit -- CString", () => {
    it("should emit simple cstrings", function () {
        checkTestEmitMainFunction("public function main(): CString { return ''; }", 'CString Mainᕒmain() { return ""_cs; }');
        checkTestEmitMainFunction("public function main(): CString { return 'abc'; }", 'CString Mainᕒmain() { return "abc"_cs; }');
        
    });

    it("should emit escaped strings", function () {
        checkTestEmitMainFunction("public function main(): CString { return '%x59;'; }", 'CString Mainᕒmain() { return "Y"_cs; }');
        checkTestEmitMainFunction("public function main(): CString { return '%%;'; }", 'CString Mainᕒmain() { return "%"_cs; }');
        checkTestEmitMainFunction("public function main(): CString { return '%;'; }", 'CString Mainᕒmain() { return "\'"_cs; }');
    });
});
