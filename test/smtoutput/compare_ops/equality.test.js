"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- basic equals", () => {
    it("should SMT exec compare simple types", function () {
        runishMainCodeUnsat("public function main(): Bool { return 0n == 1n; }", "(assert Main@main)");
        runishMainCodeUnsat("public function main(): Bool { return +2i == 2i; }", "(assert (not Main@main))");
    });
});

describe ("SMT -- basic !equal", () => {
    it("should SMT exec compare simple types", function () {
        runishMainCodeUnsat("public function main(): Bool { return 0n != 1n; }", "(assert (not Main@main))");
        runishMainCodeUnsat("public function main(): Bool { return +2i != 2i; }", "(assert Main@main)");
    });
});
/*
describe ("Exec -- enum strict equals", () => {
    it("should exec enum strict equals operations", function () {
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f === Foo#f; }", "true");
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f !== Foo#f; }", "false");

        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f === Foo#g; }", "false");
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f !== Foo#g; }", "true");
    });
});
*/