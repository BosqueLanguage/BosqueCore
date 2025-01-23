"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- simple debug", () => {
    it("should exec simple debug", function () {
        runMainCode("public function main(): Int { if(false) { _debug 5i; } return 1i; }", "1i");
    });
});
