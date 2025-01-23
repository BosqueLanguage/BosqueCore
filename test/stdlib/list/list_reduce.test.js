"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("List -- reduce simple", () => {
    it("should do simple bool reduce", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{}.reduce<Bool>(false, fn(acc, x) => acc && x > 0i); }', "false");

        runMainCode('public function main(): Bool { return List<Int>{1i, 3i}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{2i, 0i, 3i}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "false");
    });

    it("should do simple bool reduce", function () {
        runMainCode('public function main(): Int { return List<Int>{}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "0i");
        runMainCode('public function main(): Int { return List<Int>{}.reduce<Int>(5i, fn(acc, x) => acc + x); }', "5i");

        runMainCode('public function main(): Int { return List<Int>{1i, 3i}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "4i");
        runMainCode('public function main(): Int { return List<Int>{-2i, 0i, 3i}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "1i");
    });
});

