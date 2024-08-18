"use strict";

import { parseTestFunctionInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- type decl of strings w/o constraints", () => {
    it("should parse string options type decl", function () {
        parseTestFunctionInFile('type SV1 = String; [FUNC]', 'function main(): SV1 { return "ok"<SV1>; }');  
        parseTestFunctionInFile("type SV2 = CString; [FUNC]", "function main(): SV2 { return 'ok'<SV2>; }");  
    });
});

describe ("Parser -- type decl of strings w/ constraints", () => {
    it("should parse string options type decl", function () {
        parseTestFunctionInFile('type SV1 = String of /[a-z]+/; [FUNC]', 'function main(): SV1 { return "abc"<SV1>; }');  
        parseTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; [FUNC]", "function main(): SV2 { return '3'<SV2>; }");  
    });
});
