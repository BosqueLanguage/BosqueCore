"use strict";

import { parseTestFunction } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- basic Agent decls", () => {
    it ("should parse a simple Agent decl", () => {
        parseTestFunction('abstract agent main(v: Int): Int ;', undefined);
        parseTestFunction('public agent main(v: Int): Int { return 3i; }', undefined);

        parseTestFunction('abstract agent main(v: Int): Int configs { priority=immediate };', undefined);
    });
});
