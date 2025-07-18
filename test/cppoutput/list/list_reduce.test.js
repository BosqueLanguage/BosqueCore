"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPP Emit Evaluate List -- reduce simple", () => {
    it("should do simple bool reduce", function () {
        runMainCode('public function main(): Bool { return List<Int>{}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{}.reduce<Bool>(false, fn(acc, x) => acc && x > 0i); }', "false");

        runMainCode('public function main(): Bool { return List<Int>{1i, 3i}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "true");
        runMainCode('public function main(): Bool { return List<Int>{2i, 0i, 3i}.reduce<Bool>(true, fn(acc, x) => acc && x > 0i); }', "false");
    });

    it("should do simple int reduce", function () {
        runMainCode('public function main(): Int { return List<Int>{}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "0_i");
        runMainCode('public function main(): Int { return List<Int>{}.reduce<Int>(5i, fn(acc, x) => acc + x); }', "5_i");

        runMainCode('public function main(): Int { return List<Int>{1i, 3i}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "4_i");
        runMainCode('public function main(): Int { return List<Int>{-2i, 0i, 3i}.reduce<Int>(0i, fn(acc, x) => acc + x); }', "1_i");
    });

/*
    it("should do simple int reduce smt w/err", function () {
        runMainCode('public function main(): Bool { return List<Int>{1i, 3i}.reduce<Bool>(true, fn(acc, x) => { assert x != 0i; return acc && x > 0i; }); }', "(assert (not (= (@Result-ok true) Main@main)))");
        runMainCode('public function main(): Bool { return List<Int>{1i, 0i, 3i}.reduce<Bool>(true, fn(acc, x) => { assert x != 0i; return acc && x > 0i; }); }', "(assert (not (is-@Result-err Main@main)))");

        runMainCode('public function main(): Int { return List<Int>{-2i, 3i}.reduce<Int>(0i, fn(acc, x) => { assert x != 0i; return acc + x; }); }', "(assert (not (= (@Result-ok 1) Main@main)))");
        runMainCode('public function main(): Int { return List<Int>{-2i, 0i, 3i}.reduce<Int>(0i, fn(acc, x) => { assert x != 0i; return acc + x; }); }', "(assert (not (is-@Result-err Main@main)))");
    });
*/
});