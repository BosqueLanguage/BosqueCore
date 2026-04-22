"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- FCString", () => {
    it("should emit simple fcstrings", function () {
        checkTestEmitMainFunction("public function main(): CString { let v = $'${0}'; return 'a'; }", 'CString Mainᕒmain() { FCStringᐸCStringᐪCStringᐳ v = ᐸRuntimeᐳ::XFCString{0}; return ᐸRuntimeᐳ::XCString::smliteral("a"); }');
        checkTestEmitMainFunction("public function main(): CString { let v = $'${0}-${1}'; return 'a'; }", 'CString Mainᕒmain() { FCStringᐸCStringᐪCStringᐪCStringᐳ v = ᐸRuntimeᐳ::XFCString{0}; return ᐸRuntimeᐳ::XCString::smliteral("a"); }');
        checkTestEmitMainFunction("public function main(): CString { let v = $'${0: CString}-${0}'; return 'a'; }", 'CString Mainᕒmain() { FCStringᐸCStringᐪCStringᐳ v = ᐸRuntimeᐳ::XFCString{0}; return ᐸRuntimeᐳ::XCString::smliteral("a"); }');

        checkTestEmitMainFunction("public function main(): CString { let v = $'ok ${arg}'; return 'a'; }", 'CString Mainᕒmain() { FCStringᐸCStringᐪargᕀCStringᐳ v = ᐸRuntimeᐳ::XFCString{0}; return ᐸRuntimeᐳ::XCString::smliteral("a"); }');
        checkTestEmitMainFunction("public function main(): CString { let v = $'ok ${arg: CString}+${arg}'; return 'a'; }", 'CString Mainᕒmain() { FCStringᐸCStringᐪargᕀCStringᐳ v = ᐸRuntimeᐳ::XFCString{0}; return ᐸRuntimeᐳ::XCString::smliteral("a"); }');
    });
});

