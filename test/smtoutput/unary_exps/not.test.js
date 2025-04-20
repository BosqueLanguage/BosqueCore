"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- Simple Boolean not", () => {
    it("should SMT exec simple not", function () {
        runishMainCodeUnsat("public function main(x: Bool): Bool { return !x; }", "(assert (not (Main::main false)))");
        runishMainCodeUnsat("public function main(x: Bool): Bool { return !!x; }", "(assert (not (Main::main true)))");
    });
});
