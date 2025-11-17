"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- simple return", () => {
    it("should parse simple returns", function () {
        parseTestFunctionInFile('[FUNC]', 'function main(): Int { return 2i; }');
        parseTestFunctionInFile('[FUNC]', 'function main() { return; }');
    });
});
