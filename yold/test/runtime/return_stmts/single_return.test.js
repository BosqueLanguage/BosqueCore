"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- simple return", () => {
    it("should exec simple returns", function () {
        runMainCode('public function main(): Int { return 2i; }', "2i");
    });
});
