"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- logical and", () => {
    it("should exec simple and", function () {
        runTestSet("public function main(x: Bool): Bool { return x && !x; }", [['true', 'false'], ['false', 'false']], []);
        runTestSet("type Foo = Bool; public function main(x: Foo): Foo { return x && !x; }", [['true<Main::Foo>', 'false<Main::Foo>'], ['false<Main::Foo>', 'false<Main::Foo>']], []);
    });
});
