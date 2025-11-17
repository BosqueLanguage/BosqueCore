"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- logical implies", () => {
    it("should exec simple implies", function () {
        runMainCode("public function main(): Bool { return true ==> false; }", "false");
        runMainCode("public function main(): Bool { return false ==> true; }", "true");
    });

    it("should exec sc implies", function () {
        runMainCode("public function main(): Bool { return false ==> (1i // 0i) == 1i; }", "true");
    });
});
