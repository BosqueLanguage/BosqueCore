"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- basic equals", () => {
    it("should exec compare simple types", function () {
        runMainCode("public function main(): Bool { return 0n == 1n; }", [false, "Bool"]);
        runMainCode("public function main(): Bool { return +2i == 2i; }", [true, "Bool"]);
    });
});

describe ("Exec -- basic !equal", () => {
    it("should exec compare simple types", function () {
        runMainCode("public function main(): Bool { return 0n != 1n; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { return +2i != 2i; }", [false, "Bool"]);
    });
});

describe ("Exec -- enum strict equals", () => {
    it("should exec enum strict equals operations", function () {
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f === Foo#f; }", [true, "Bool"]);
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f !== Foo#f; }", [false, "Bool"]);

        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f === Foo#g; }", [false, "Bool"]);
        runMainCode("enum Foo { f, g } public function main(): Bool { return Foo#f !== Foo#g; }", [true, "Bool"]);
    });
});
