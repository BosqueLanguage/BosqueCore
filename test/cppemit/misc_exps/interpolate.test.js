"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- interpolate cstring", () => {
    it("should emit simple interpolate cstring", function () {
        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring($'-${0}-', 'a'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<1>(ᐸRuntimeᐳ::XFCString{0}.fcid, { "a"_cs }); }');
        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring($'${0}-${1}', 'a', 'b'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<2>(ᐸRuntimeᐳ::XFCString{0}.fcid, { "a"_cs, "b"_cs }); }');

        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring<CString>($'${0}-${0}', 'a'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<1>(ᐸRuntimeᐳ::XFCString{0}.fcid, { "a"_cs }); }');
        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring<CString>($'${arg2}-${arg1}', arg1 = 'a', arg2 = 'b'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<2>(ᐸRuntimeᐳ::XFCString{0}.fcid, { "a"_cs, "b"_cs }); }');
        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring<CString>($'${arg1}-${arg1}', arg1 = 'a'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<1>(ᐸRuntimeᐳ::XFCString{0}.fcid, { "a"_cs }); }');
    });
});

describe ("CPPEmit -- interpolate string", () => {
    it("should emit simple interpolate string", function () {
        checkTestEmitMainFunction('public function main(): String { return Interpolate::string($"-${0}-", "a"); }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XFString::interpolate<1>(ᐸRuntimeᐳ::XFString{0}.fcid, { U"a"_us }); }');
        checkTestEmitMainFunction('public function main(): String { return Interpolate::string($"${0}-${1}", "a", "b"); }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XFString::interpolate<2>(ᐸRuntimeᐳ::XFString{0}.fcid, { U"a"_us, U"b"_us }); }');

        checkTestEmitMainFunction('public function main(): String { return Interpolate::string<String>($"${0}-${0}", "a"); }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XFString::interpolate<1>(ᐸRuntimeᐳ::XFString{0}.fcid, { U"a"_us }); }');
        checkTestEmitMainFunction('public function main(): String { return Interpolate::string<String>($"${arg2}-${arg1}", arg1 = "a", arg2 = "b"); }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XFString::interpolate<2>(ᐸRuntimeᐳ::XFString{0}.fcid, { U"a"_us, U"b"_us }); }');
        checkTestEmitMainFunction('public function main(): String { return Interpolate::string<String>($"${arg1}-${arg1}", arg1 = "a"); }', 'String Mainᕒmain() { return ᐸRuntimeᐳ::XFString::interpolate<1>(ᐸRuntimeᐳ::XFString{0}.fcid, { U"a"_us }); }');
    });
});
