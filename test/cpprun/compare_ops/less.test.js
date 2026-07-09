"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- basic less", () => {
    it("should exec compare simple types", function () {
        runTestSet("public function main(x: Nat): Bool { return x < 1n; }", [['1n', 'false'], ['0n', 'true'], ['10n', 'false']], []);
        runTestSet("public function main(x: Int): Bool { return 2i < x; }", [['2i', 'false'], ['0i', 'false'], ['-10i', 'false']], []);
        runTestSet("public function main(x: ChkInt): Bool { return x < ChkInt::npos; }", [['2I', 'true'], ['ChkInt::npos', 'false']], []);
    });

    it("should exec compare type alias", function () {
        runTestSet("type Foo = Int; public function main(x: Foo): Bool { return 0i<Foo> < x; }", [['2i<Main::Foo>', 'true'], ['0i<Main::Foo>', 'false'], ['-10i<Main::Foo>', 'false']], []);
    });
});

describe ("CPPExec -- basic less or equal", () => {
    it("should exec compare simple types", function () {
        runTestSet("public function main(x: Nat): Bool { return x <= 1n; }", [['1n', 'true'], ['0n', 'true'], ['10n', 'false']], []);
        runTestSet("public function main(x: Int): Bool { return 2i <= x; }", [['2i', 'true'], ['0i', 'false'], ['-10i', 'false']], []);
        runTestSet("public function main(x: ChkInt): Bool { return x <= ChkInt::npos; }", [['2I', 'true'], ['ChkInt::npos', 'true']], []);
    });

    it("should exec compare type alias", function () {
        runTestSet("type Foo = Int; public function main(x: Foo): Bool { return 0i<Foo> <= x; }", [['2i<Main::Foo>', 'true'], ['0i<Main::Foo>', 'true'], ['-10i<Main::Foo>', 'false']], []);
    });
});
