"use strict";

import { parseTestFunction } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Debug", () => {
    it("should parse debug", function () {
        parseTestFunction("function main(): Int { _debug 5i; return 1i; }", undefined);
    });
});

