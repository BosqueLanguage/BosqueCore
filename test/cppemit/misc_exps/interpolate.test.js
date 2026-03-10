"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- interpolate cstring", () => {
    it("should emit simple interpolate cstring", function () {
        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring($'-${0}-', 'a'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<1>(ᐸRuntimeᐳ::XFCString{0}.fcid, { ᐸRuntimeᐳ::XCString::smliteral("a") }); }');
        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring($'${0}-${1}', 'a', 'b'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<2>(ᐸRuntimeᐳ::XFCString{0}.fcid, { ᐸRuntimeᐳ::XCString::smliteral("a"), ᐸRuntimeᐳ::XCString::smliteral("b") }); }');

        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring<CString>($'${0}-${0}', 'a'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<1>(ᐸRuntimeᐳ::XFCString{0}.fcid, { ᐸRuntimeᐳ::XCString::smliteral("a") }); }');
        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring<CString>($'${arg2}-${arg1}', arg1 = 'a', arg2 = 'b'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<2>(ᐸRuntimeᐳ::XFCString{0}.fcid, { ᐸRuntimeᐳ::XCString::smliteral("a"), ᐸRuntimeᐳ::XCString::smliteral("b") }); }');
        checkTestEmitMainFunction("public function main(): CString { return Interpolate::cstring<CString>($'${arg1}-${arg1}', arg1 = 'a'); }", 'CString Mainᕒmain() { return ᐸRuntimeᐳ::XFCString::interpolate<1>(ᐸRuntimeᐳ::XFCString{0}.fcid, { ᐸRuntimeᐳ::XCString::smliteral("a") }); }');
    });
});

