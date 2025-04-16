"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Just make sure we can create cchar", () => {
    it("CChar create", function () {
        runMainCode("public function main(): CChar { return b''; }", "''"); 
    });
});
