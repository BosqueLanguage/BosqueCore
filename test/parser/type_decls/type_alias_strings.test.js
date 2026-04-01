"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- type decl of strings w/o constraints", () => {
    it("should parse string options type decl", function () {
        parseTestFunctionInFile('type SV1 = String; [FUNC]', 'function main(): SV1 { return "ok"<SV1>; }');  
        parseTestFunctionInFile("type SV2 = CString; [FUNC]", "function main(): SV2 { return 'ok'<SV2>; }");  
    });
});

describe ("Parser -- type decl of strings w/ size constraints", () => {
    it("should parse string options type decl", function () {
        parseTestFunctionInFile('type SV1 = String{1n, 3n}; [FUNC]', 'function main(): SV1 { return "abc"<SV1>; }');  
        parseTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString{1n, 5n} of Main::re2; [FUNC]", "function main(): SV2 { return '3'<SV2>; }");  

        parseTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString{3n} of Main::re2; [FUNC]", "function main(): SV2 { return '3'<SV2>; }");  
        parseTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString{, 3n} of Main::re2; [FUNC]", "function main(): SV2 { return '3'<SV2>; }");  
        parseTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString{3n, } of Main::re2; [FUNC]", "function main(): SV2 { return '3'<SV2>; }");  
    });

    it("should parse fail string options type decl", function () {
        parseTestFunctionInFileError('type SV1 = String{1, 3n}; function main(): SV1 { return "abc"<SV1>; }', "Unknown member ;");
        parseTestFunctionInFileError('type SV1 = String{1n 3n}; function main(): SV1 { return "abc"<SV1>; }', 'Expected "}" but got "3n" when parsing "type declaration size range"');

        parseTestFunctionInFileError('type SV1 = String{1i, 3i}; function main(): SV1 { return "abc"<SV1>; }', "Range bound literal must match type String");  
    });
});

describe ("Parser -- type decl of strings w/ regex constraints", () => {
    it("should parse string options type decl", function () {
        parseTestFunctionInFile('type SV1 = String of /[a-z]+/; [FUNC]', 'function main(): SV1 { return "abc"<SV1>; }');  
        parseTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; [FUNC]", "function main(): SV2 { return '3'<SV2>; }");  
    });

    it("should parse fail string options type decl", function () {
        parseTestFunctionInFileError('type SV1 = String /[a-z]+/; function main(): SV1 { return "abc"<SV1>; }', 'Expected "&" but got "/[a-z]+/" when parsing "type declaration"');
    });
});

describe ("Parser -- type decl of strings w/ both regex and size constraints", () => {
    it("should parse string options type decl", function () {
        parseTestFunctionInFile('type SV1 = String{1n, 3n} of /[a-z]+/; [FUNC]', 'function main(): SV1 { return "abc"<SV1>; }');  
        parseTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString{1n} of Main::re2; [FUNC]", "function main(): SV2 { return '3'<SV2>; }");  
    });
});
