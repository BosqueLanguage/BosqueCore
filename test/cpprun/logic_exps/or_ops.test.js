"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- logical or", () => {
    it("should exec simple or", function () {
        runTestSet("public function main(x: Bool): Bool { return x || !x; }", [['true', 'true'], ['false', 'true']], []);
        runTestSet("type Foo = Bool; public function main(x: Foo): Foo { return x || !x; }", [['true<Main::Foo>', 'true<Main::Foo>'], ['false<Main::Foo>', 'true<Main::Foo>']], []);
    });
});
