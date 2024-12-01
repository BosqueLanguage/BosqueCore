"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- reduce simple", () => {
    it("should do simple bool reduce", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', [true, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{}.reduce<Bool>(false, fn(acc, x) => acc && x > 0i); }', [false, "Bool"]);

        runMainCode('public function main(): Bool { return List<Int>{1i, 3i}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', [true, "Bool"]);
        runMainCode('public function main(): Bool { return List<Int>{2i, 0i, 3i}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', [false, "Bool"]);
    });

    it("should do simple bool reduce", function () {
        runMainCode('public function main(): Int { return List<Int>{}.reduce<Int>(0i, fn(acc, x) => acc + x); }', [0n, "Int"]);
        runMainCode('public function main(): Int { return List<Int>{}.reduce<Int>(5i, fn(acc, x) => acc + x); }', [5n, "Int"]);

        runMainCode('public function main(): Int { return List<Int>{1i, 3i}.reduce<Int>(0i, fn(acc, x) => acc + x); }', [4n, "Int"]);
        runMainCode('public function main(): Int { return List<Int>{-2i, 0i, 3i}.reduce<Int>(0i, fn(acc, x) => acc + x); }', [1n, "Int"]);
    });
});

