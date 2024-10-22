"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- op and", () => {
    it("should exec simple and", function () {
        runMainCode("public function main(): Bool { return /\\(true); }", [true, "Bool"]);
        runMainCode("public function main(): Bool { return /\\(true, false); }", [false, "Bool"]);
        runMainCode("public function main(): Bool { return /\\(true, false, true); }", [false, "Bool"]);
    });
});
