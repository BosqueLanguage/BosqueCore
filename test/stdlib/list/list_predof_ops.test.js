"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- allof basic", () => {
    it("should do simple allof", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.allOf(pred(x) => x >= 0i); }', [true, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i}.allOf(pred(x) => x >= 0i); }', [true, "Bool"]);

        runMainCode('public function main(): Bool { return List<Int>{-2i}.allOf(pred(x) => x >= 0i); }', [false, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{1i, -1i}.allOf(pred(x) => x >= 0i); }', [false, "Bool"]);
    });
});

describe ("List -- noneof basic", () => {
    it("should do simple noneof", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.noneOf(pred(x) => x >= 0i); }', [true, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{-1i, -2i}.noneOf(pred(x) => x >= 0i); }', [true, "Bool"]);

        runMainCode('public function main(): Bool { return List<Int>{2i}.noneOf(pred(x) => x >= 0i); }', [false, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{1i, -1i}.noneOf(pred(x) => x >= 0i); }', [false, "Bool"]);
    });
});

describe ("List -- someof basic", () => {
    it("should do simple someof", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.someOf(pred(x) => x >= 0i); }', [false, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{-1i, 2i}.someOf(pred(x) => x >= 0i); }', [true, "Bool"]);

        runMainCode('public function main(): Bool { return List<Int>{-2i}.someOf(pred(x) => x >= 0i); }', [false, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{-1i, -1i}.someOf(pred(x) => x >= 0i); }', [false, "Bool"]);
    });
});
