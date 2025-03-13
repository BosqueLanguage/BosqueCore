"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- find basic", () => {
    it("should do simple find", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.find(pred(x) => x >= 0i)?none; }', "true");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i, 1i}.find(pred(x) => x >= 2i)@some; }', "2i");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.find(pred(x) => x >= 4i)?none; }', "true");
    });
});

describe ("List -- findLast basic", () => {
    it("should do simple find", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.findLast(pred(x) => x >= 0i)?none; }', "true");
        runMainCode('public function main(): Int { return List<Int>{1i, 2i, 3i, 1i}.findLast(pred(x) => x >= 2i)@some; }', "3i");
        runMainCode('public function main(): Bool { return List<Int>{1i, 2i, 3i}.findLast(pred(x) => x >= 4i)?none; }', "true");
    });
});
