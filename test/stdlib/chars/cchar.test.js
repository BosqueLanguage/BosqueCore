"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("test char creation", () => {
    it("cchar create", function () {
        runMainCode("public function main(): CChar { return c''; }", "''"); 
        runMainCode("public function main(): CChar { return c'z'; }", "'z'");
    });
    it("cchar fail multiple", function () { // Caught by type checker
        runMainCodeError("public function main(): CChar { return c'aa'; }", "[FAILED TO BUILD ASSEMBLY] public function main(): CChar { return c'aa'; }");
    });
    it("cchar equality", function () {
        runMainCode("public function main(): Bool { return c'a' === c'a'; }", "true"); 
        runMainCode("public function main(): Bool { return c'a' !== c'a'; }", "false");
    });
    it("unicodechar create", function () {
        runMainCode("public function main(): UnicodeChar { return c\"a\"; }", "\"a\"");
        runMainCode("public function main(): UnicodeChar { return c\"\"; }", "\"\""); 
        runMainCode("public function main(): UnicodeChar { return c\"星\"; }", "\"星\"");
    });
    it("unicodechar fail multiple", function () {
        runMainCodeError("public function main(): UnicodeChar { return c\"a星\"; }", "[FAILED TO BUILD ASSEMBLY] public function main(): UnicodeChar { return c\"a星\"; }");
    });
    it("unicodechar equality", function () {
        runMainCode("public function main(): Bool { return c\"a\" === c\"a\"; }", "true");
        runMainCode("public function main(): Bool { return c\"星\" !== c\"星\"; }", "false"); 
    });
});
