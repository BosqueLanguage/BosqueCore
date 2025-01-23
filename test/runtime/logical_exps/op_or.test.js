"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- op or", () => {
    it("should exec simple or", function () {
        runMainCode("public function main(): Bool { return \\/(true); }", "true");
        runMainCode("public function main(): Bool { return \\/(true, false); }", "true");
        runMainCode("public function main(): Bool { return \\/(false, false, false); }", "false");
    });
});
