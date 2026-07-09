"use strict";

import { parseTestFunction } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- basic API decls", () => {
    it ("should parse a simple API decl", () => {
        parseTestFunction('abstract api main(v: Int): Int ;', undefined);
        parseTestFunction('public api main(v: Int): Int { return 3i; }', undefined);

        parseTestFunction('abstract api main(v: Int): Int configs { priority=immediate };', undefined);
    });
});
