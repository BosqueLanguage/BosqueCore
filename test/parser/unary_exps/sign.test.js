"use strict";

import { parseTestExp, parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Sign", () => {
    it("should parse simple sign", function () {
        parseTestExp("+(5i)", undefined, "Int");
        parseTestExp("-(3i)", undefined, "Int");
        parseTestExp("-(-3i)", undefined, "Int");
    });

    it("should parse typedecl sign", function () {
        parseTestFunctionInFile("type IsFooEnabled = Int; [FUNC]", "function main(): IsFooEnabled { return +(5i<IsFooEnabled>); }");
        parseTestFunctionInFile("type IsFooEnabled = Int; [FUNC]", "function main(): IsFooEnabled { return -(3i<IsFooEnabled>); }");
    });
});

