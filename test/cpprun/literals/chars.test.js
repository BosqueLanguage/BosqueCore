"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- CChar", () => {
    it("should exec simple chars", function () {
        runTestSet("public function main(): CChar { return c'x'; }", [[undefined, "c'x'"]], []);
        runTestSet("public function main(c: CChar): CChar { return c; }", [['c"a"', "c'a'"], ['c"%x59;"', "c'Y'"], ['c"%%;"', "c'%%;'"]], []);

        runTestSet("public function main(): CChar { return c'%;'; }", [[undefined, "c'%;'"]], []);
 
    });
});

describe ("CPPExec -- UnicodeChar", () => {
    it("should exec simple uchars", function () {
        runTestSet("public function main(): UnicodeChar { return c\"x\"; }", [[undefined, 'c"x"']], []);
        runTestSet("public function main(): UnicodeChar { return c\"🌵\"; }", [[undefined, 'c"🌵"']], []);

        runTestSet("public function main(c: UnicodeChar): UnicodeChar { return c; }", [['c"a"', 'c"a"'], ['c"%x59;"', 'c"Y"'], ['c"%%;"', 'c"%%;"']], []);
    });
});
