"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- basic greater", () => {
    it("should exec compare simple types", function () {
        runTestSet("public function main(x: Nat): Bool { return x > 1n; }", [['1n', 'false'], ['0n', 'false'], ['10n', 'true']], []);
        runTestSet("public function main(x: Int): Bool { return 2i > x; }", [['2i', 'false'], ['0i', 'true'], ['-10i', 'true']], []);
        runTestSet("public function main(x: ChkInt): Bool { return x > ChkInt::npos; }", [['2I', 'false'], ['ChkInt::npos', 'false']], []);
    });

    it("should exec compare type alias", function () {
        runTestSet("type Foo = Int; public function main(x: Foo): Bool { return 0i<Foo> > x; }", [['2i<Main::Foo>', 'false'], ['0i<Main::Foo>', 'false'], ['-10i<Main::Foo>', 'true']], []);
    });
});

describe ("CPPExec -- basic greater or equal", () => {
    it("should exec compare simple types", function () {
        runTestSet("public function main(x: Nat): Bool { return x >= 1n; }", [['1n', 'true'], ['0n', 'false'], ['10n', 'true']], []);
        runTestSet("public function main(x: Int): Bool { return 2i >= x; }", [['2i', 'true'], ['0i', 'true'], ['-10i', 'true']], []);
        runTestSet("public function main(x: ChkInt): Bool { return x >= ChkInt::npos; }", [['2I', 'false'], ['ChkInt::npos', 'true']], []);
    });

    it("should exec compare type alias", function () {
        runTestSet("type Foo = Int; public function main(x: Foo): Bool { return 0i<Foo> >= x; }", [['2i<Main::Foo>', 'false'], ['0i<Main::Foo>', 'true'], ['-10i<Main::Foo>', 'true']], []);
    });
});
