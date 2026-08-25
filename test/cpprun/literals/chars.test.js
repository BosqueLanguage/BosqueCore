"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- CChar", () => {
    it("should exec simple chars", function () {
        runTestSet("public function main(c: CChar): CChar { return c'x'; }", [['c"a"', "c'x'"]], []);
        runTestSet("public function main(c: CChar): CChar { return c; }", [['c"a"', "c'a'"], ['c"%x59;"', "c'Y'"], ['c"%%;"', "c'%%;'"]], []);

        runTestSet("public function main(c: CChar): CChar { return c'%;'; }", [['c"a"', "c'%;'"]], []);
 
    });
});

describe ("CPPExec -- UnicodeChar", () => {
    it("should exec simple uchars", function () {
        runTestSet("public function main(c: UnicodeChar): UnicodeChar { return c\"x\"; }", [['c"a"', 'c"x"']], []);
        runTestSet("public function main(c: UnicodeChar): UnicodeChar { return c\"🌵\"; }", [['c"a"', 'c"%x1f335;"']], []);

        runTestSet("public function main(c: UnicodeChar): UnicodeChar { return c; }", [['c"a"', 'c"a"'], ['c"🌵"', 'c"%x1f335;"'], ['c"%x59;"', 'c"Y"'], ['c"%%;"', 'c"%%;"']], []);
    });
});
