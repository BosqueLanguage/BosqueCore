"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("exec -- special literals", () => {
    it("should exec true", function () {
        runMainCode("public function main(): Bool { return true; }", "true");
    });

    it("should exec false", function () {
        runMainCode("public function main(): Bool { return false; }", "false");
    });
});
