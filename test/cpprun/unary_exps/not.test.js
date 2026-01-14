"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple Boolean not", () => {
    it("should exec simple not", function () {
        runTestSet("public function main(x: Bool): Bool { return !x; }", [['true', 'false'], ['false', 'true']], []);
        runTestSet("public function main(x: Bool): Bool { return !!x; }", [['true', 'true'], ['false', 'false']], []);
    });

    it("should exec type alias not", function () {
        runTestSet("type Foo = Bool; public function main(x: Foo): Foo { return !x; }", [['true<Main::Foo>', 'false<Main::Foo>'], ['false<Main::Foo>', 'true<Main::Foo>']], []);
        runTestSet("type Foo = Bool; public function main(x: Foo): Foo { return !!x; }", [['true<Main::Foo>', 'true<Main::Foo>'], ['false<Main::Foo>', 'false<Main::Foo>']], []);
    });
});
