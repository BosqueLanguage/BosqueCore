"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- logical or", () => {
    it("should exec simple or", function () {
        runMainCode("public function main(): Bool { return true || false; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { return false || false; }", [false, "Bool"]);
    });

    it("should exec sc or", function () {
        runMainCode("public function main(): Bool { return true || (1i // 0i) == 1i; }", [true, "Bool"]);
    });
});
