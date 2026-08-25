"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";


describe ("CPPEmit -- CChar", () => {
    it("should check simple chars", function () {
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c'x'; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{'x'}; }");
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c' '; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{' '}; }");
        
    });

    it("should check escaped chars", function () {
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c'%x59;'; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{'Y'}; }");
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c'%%;'; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{'%'}; }");
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c'%;'; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{'\\''}; }");
    });
});

describe ("CPPEmit -- UnicodeChar", () => {
    it("should check simple uchars", function () {
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"a\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{'a'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"🌵\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{'🌵'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\" \"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{' '}; }");
    });

    it("should check escaped strings", function () {
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"%x59;\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{'Y'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"%x1f335;\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{'🌵'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"%%;\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{'%'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"%;\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{'\"'}; }");
    });
});