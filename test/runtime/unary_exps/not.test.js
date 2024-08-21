"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Simple Boolean not", () => {
    it("should exec simple not", function () {
        runMainCode("public function main(): Bool { return !false; }", [true, "Bool"]);
        runMainCode("public function main(): Bool { return !!true; }", [true, "Bool"]);
    });
});
