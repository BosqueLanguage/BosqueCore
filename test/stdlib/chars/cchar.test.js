"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("test char creation", () => {
    it("cchar create", function () {
        runMainCode("public function main(): CChar { return b''; }", "''"); 
        runMainCode("public function main(): CChar { return b'z'; }", "'z'");
    });
    it("cchar equality", function () {
        runMainCode("public function main(): Bool { return b'a' === b'a'; }", "true"); 
        runMainCode("public function main(): Bool { return b'a' !== b'a'; }", "false");
    });
    it("unicodechar create", function () {
        runMainCode("public function main(): UnicodeChar { return u'a'; }", "'a'");
        runMainCode("public function main(): UnicodeChar { return u''; }", "''"); 
        runMainCode("public function main(): UnicodeChar { return u'星'; }", "'星'");
    });
    it("unicodechar equality", function () {
        runMainCode("public function main(): Bool { return u'a' === u'a'; }", "true");
        runMainCode("public function main(): Bool { return u'星' !== u'星'; }", "false"); 
    });
});
