"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- basic KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runTestSet("public function main(x: Nat): Bool { return KeyComparator::equal<Nat>(x, 1n); }", [['1n', 'true'], ['3n', 'false']], []);
        runTestSet("public function main(x: Nat): Bool { return KeyComparator::less<Nat>(1n, x); }", [['1n', 'false'], ['3n', 'true'], ['0n', 'false']], []);

        runTestSet("public function main(x: String): Bool { return KeyComparator::equal<CString>(\"ok\", x); }", [['""', 'false'], ['"ok"', 'true'], ['"oj"', 'false']], []);
        runTestSet("public function main(x: String): Bool { return KeyComparator::less<CString>(x, \"ok\"); }", [['""', 'true'], ['"w"', 'true'], ['"ok"', 'false'], ['"oj"', 'true'], ['"ow"', 'false'], ['"ajk"', 'false']], []);
    });
});

describe ("CPPExec -- type alias KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runTestSet("type Foo = Int; public function main(x: Foo): Bool { return KeyComparator::equal<Foo>(x, 1i<Foo>); }", [['1i<Foo>', 'true'], ['3i<Foo>', 'false']], []);
        runTestSet("type Foo = Int; public function main(x: Foo): Bool { return KeyComparator::less<Foo>(x, 1i<Foo>); }", [['1i<Foo>', 'false'], ['3i<Foo>', 'false'], ['-3i<Foo>', 'true'], ['0i<Foo>', 'true']], []);
    });
});

describe ("CPPExec -- enum KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runTestSet("enum Foo { f, g, h } public function main(x: Foo): Bool { return KeyComparator::equal<Foo>(Foo#f, x); }", [['Main::foo#f', 'true'], ['Main::foo#h', 'false']], []);
        runTestSet("enum Foo { f, g, h } public function main(x: Foo): Bool { return KeyComparator::less<Foo>(x, Foo#g); }", [['Main::foo#f', 'true'], ['Main::foo#g', 'false'], ['Main::foo#h', 'false']], []);
    });
});
