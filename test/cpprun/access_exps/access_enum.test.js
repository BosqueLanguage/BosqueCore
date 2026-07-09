"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- access enum", () => {
    it("should exec simple enum access", function () {
        runTestSet("enum Foo {f, g} public function main(x: Int): Foo { return Foo#f; }", [], []);
        runTestSet("enum Foo {f, g} public function main(f: Foo): Foo { return f; }", [['Main::Foo#f', 'Main::Foo#f'], ['Main::Foo#g', 'Main::Foo#g']], []);
    });
});
