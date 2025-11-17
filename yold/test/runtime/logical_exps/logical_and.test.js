"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- logical and", () => {
    it("should exec simple and", function () {
        runMainCode("public function main(): Bool { return true && false; }", "false");
        runMainCode("public function main(): Bool { return true && true; }", "true");
    });

    it("should exec sc and", function () {
        runMainCode("public function main(): Bool { return false && (1i // 0i) == 1i; }", "false");
    });
});
