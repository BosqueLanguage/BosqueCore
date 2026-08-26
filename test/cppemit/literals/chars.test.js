"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- CChar", () => {
    it("should emit simple chars", function () {
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c'x'; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{'x'}; }");
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c' '; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{' '}; }");
        
    });

    it("should emit escaped chars", function () {
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c'%x59;'; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{'Y'}; }");
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c'%%;'; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{'%'}; }");
        checkTestEmitMainFunction("public function main(c: CChar): CChar { return c'%;'; }", "CChar Mainᕒmain(CChar c) { return ᐸRuntimeᐳ::XCChar{'\\''}; }");
    });
});

describe ("CPPEmit -- UnicodeChar", () => {
    it("should emit simple uchars", function () {
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"a\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{U'a'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"🌵\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{U'🌵'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\" \"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{U' '}; }");
    });

    it("should emit escaped strings", function () {
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"%x59;\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{U'Y'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"%x1f335;\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{U'🌵'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"%%;\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{U'%'}; }");
        checkTestEmitMainFunction("public function main(c: UnicodeChar): UnicodeChar { return c\"%;\"; }", "UnicodeChar Mainᕒmain(UnicodeChar c) { return ᐸRuntimeᐳ::XUnicodeChar{U'\"'}; }");
    });
});
