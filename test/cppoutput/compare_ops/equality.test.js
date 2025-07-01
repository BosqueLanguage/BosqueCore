"use strict";

import { runMainCode } from "../../../bin/test/cppoutput/cppemit_nf.js"
import { describe, it } from "node:test";

describe("CPP Emit Evalutate -- basic equals", () => {
    it("should exec compare simple types", function () {
        runMainCode("public function main(): Bool { return 0n == 1n; }", "false");
        runMainCode("public function main(): Bool { return +2i == 2i; }", "true");
    })
});

describe("CPP Emit Evalutate -- basic !equals", () => {
    it("should exec compare simple types", function () {
        runMainCode("public function main(): Bool { return 0n != 1n; }", "true");
        runMainCode("public function main(): Bool { return +2i != 2i; }", "false");
    })
});

describe ("CPP Emit Evaluate -- enum strict equals", () => {
    it("should exec enum strict equals operations", function () {
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f === Foo#f; }", "true");
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f !== Foo#f; }", "false");

        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f === Foo#g; }", "false");
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f !== Foo#g; }", "true");
    });
});
