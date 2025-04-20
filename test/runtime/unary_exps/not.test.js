"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Simple Boolean not", () => {
    it("should exec (simplify) simple not", function () {
        runMainCode("public function main(): Bool { return !false; }", "true");
        runMainCode("public function main(): Bool { return !!true; }", "true");
    });

    it("should exec simple not", function () {
        runMainCode("public function main(): Bool { let x = false; return !x; }", "true");
        runMainCode("public function main(): Bool { let x = true; return !!x; }", "true");
    });
});
