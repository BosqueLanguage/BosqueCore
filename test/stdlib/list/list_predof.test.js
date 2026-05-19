"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- allof basic", () => {
    it("should do simple allof", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.allOf(pred(x) => x >= 0i); }', [['0i', 'true']], []);
        runTestSet('public function main(z: Int): Bool { return List<Int>{1i, z, 5i}.allOf(pred(x) => x >= 0i); }', [['1i', 'true'], ['-1i', 'false']], []);
    });
});

describe ("List -- noneof basic", () => {
    it("should do simple noneof", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.noneOf(pred(x) => x >= 0i); }', [['0i', 'true']], []);
        runTestSet('public function main(z: Int): Bool { return List<Int>{-1i, z, -5i}.noneOf(pred(x) => x >= 0i); }', [['-1i', 'true'], ['2i', 'false']], []);
    });
});

describe ("List -- someof basic", () => {
    it("should do simple someof", function () {
        runTestSet('public function main(z: Int): Bool { return List<Int>{}.someOf(pred(x) => x >= 0i); }', [['0i', 'false']], []);
        runTestSet('public function main(z: Int): Bool { return List<Int>{-1i, z}.someOf(pred(x) => x >= 0i); }', [['-1i', 'false'], ['2i', 'true']], []);
    });
});
