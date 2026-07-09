"use strict";

import { parseTestExp, parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Boolean not", () => {
    it("should parse simple not", function () {
        parseTestExp("!true", undefined, "Bool");
        parseTestExp("!!true", "!(!true)", "Bool");
    });

    it("should parse typedecl not", function () {
        parseTestFunctionInFile("type IsFooEnabled = Bool; [FUNC]", "function main(): IsFooEnabled { return !true<IsFooEnabled>; }");
    });
});
