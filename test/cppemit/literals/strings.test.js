"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- String", () => {
    it("should emit simple strings", function () {
        checkTestEmitMainFunction('public function main(): String { return ""; }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XString::smliteral(U""); }');
        checkTestEmitMainFunction('public function main(): String { return "abc"; }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XString::smliteral(U"abc"); }');
        //checkTestEmitMainFunction('public function main(): String { return "a🌵c"; }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XString::smliteral(U"a🌵c"); }');
    });

    it("should emit escaped strings", function () {
        checkTestEmitMainFunction('public function main(): String { return "%x59;"; }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XString::smliteral(U"Y"); }');
        //checkTestEmitMainFunction('public function main(): String { return "%x1f335;"; }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XString::smliteral(U"🌵"); }');
        checkTestEmitMainFunction('public function main(): String { return "%%;"; }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XString::smliteral(U"%"); }');
        checkTestEmitMainFunction('public function main(): String { return "%;"; }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XString::smliteral(U"\\""); }');
    });
});

describe ("CPPEmit -- CString", () => {
    it("should emit simple cstrings", function () {
        checkTestEmitMainFunction("public function main(): CString { return ''; }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XCString::smliteral(""); }');
        checkTestEmitMainFunction("public function main(): CString { return 'abc'; }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XCString::smliteral("abc"); }');
        
    });

    it("should emit escaped strings", function () {
        checkTestEmitMainFunction("public function main(): CString { return '%x59;'; }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XCString::smliteral("Y"); }');
        checkTestEmitMainFunction("public function main(): CString { return '%%;'; }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XCString::smliteral("%"); }');
        checkTestEmitMainFunction("public function main(): CString { return '%;'; }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XCString::smliteral("\'"); }');
    });
});
