"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- access argument", () => {
    it("should check simple arg var access", function () {
        checkTestFunction("function main(x: Int): Int { return x; }", undefined);
        checkTestFunction("function main(x: Int, y: Bool): Bool { return y; }", undefined);
    });

    it("should fail simple wrong result type", function () {
        checkTestFunctionError("function main(x: Int, y: Bool): Bool { return x; }", "Expected a return value of type Bool but got Int");
    });
});
