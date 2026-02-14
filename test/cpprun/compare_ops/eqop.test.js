"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- basic strict equals", () => {
    it("should exec strict equals operations", function () {
        runTestSet("public function main(x: Nat): Bool { return 0n === x; }", [['0n', 'true'], ['1n', 'false'], ['5n', 'false']], []);
        runTestSet("public function main(x: Nat): Bool { return x !== 1n; }", [['0n', 'true'], ['1n', 'false'], ['5n', 'true']], []);
        runTestSet("public function main(x: String): Bool { return \"ok\" === x; }", [['""', 'false'], ['"ok"', 'true'], ['"yes"', 'false']], []);
    });
});

describe ("CPPExec -- Some strict equals", () => {
    it("should exec strict equals option operations", function () {
        runTestSet("public function main(y: Some<Int>): Bool { let x = 3i; return x === y; }", [['some(3i)', 'true'], ['some(4i)', 'false']], []);
        runTestSet("public function main(y: Some<Int>): Bool { let x = 4i; return y !== x; }", [['some(3i)', 'true'], ['some(4i)', 'false']], []);
    });
});

describe ("CPPExec -- Option strict equals", () => {
    it("should exec strict equals option operations", function () {
        runTestSet("public function main(x: Option<Int>): Bool { return x === none; }", [['none', 'true'], ['some(3i)', 'false']], []);
        runTestSet("public function main(x: Option<Int>): Bool { return x !== none; }", [['none', 'false'], ['some(3i)', 'true']], []);

        runTestSet("public function main(x: Option<Int>): Bool { return x === 3i; }", [['none', 'false'], ['some(3i)', 'true'], ['some(4i)', 'false']], []);
        runTestSet("public function main(x: Option<Int>): Bool { return 3i !== x; }", [['none', 'true'], ['some(3i)', 'false'], ['some(4i)', 'true']], []);
    });
});

describe ("CPPExec -- type alias strict equals", () => {
    it("should exec type alias strict equals operations", function () {
        runTestSet("type Foo = Int; public function main(x: Foo): Bool { return x === 1i<Foo>; }", [['1i<Main::Foo>', 'true'], ['-1i<Main::Foo>', 'false']], []);
        runTestSet("type Foo = Int; public function main(x: Foo): Bool { return 1i<Foo> !== x; }", [['1i<Main::Foo>', 'false'], ['-1i<Main::Foo>', 'true']], []);

        runTestSet("type Foo = Int; public function main(x: Option<Foo>): Bool { return x === none; }", [['none', 'true'], ['some(3i<Main::Foo>)', 'false']], []);
    });
});

describe ("CPPExec -- enum strict equals", () => {
    it("should check enum strict equals operations", function () {
        runTestSet("enum Foo { f, g } public function main(x: Foo): Bool { return x === Foo#f; }", [['Main::Foo#f', 'true'], ['Main::Foo#g', 'false']], []);
        runTestSet("enum Foo { f, g } public function main(x: Foo): Bool { return Foo#f !== x; }", [['Main::Foo#f', 'false'], ['Main::Foo#g', 'true']], []);

        runTestSet("enum Foo { f, g } public function main(x: Option<Foo>): Bool { return x === Foo#g; }", [['none', 'false'], ['some(Main::Foo#f)', 'false'], ['some(Main::Foo#g)', 'true']], []);
    });
});
