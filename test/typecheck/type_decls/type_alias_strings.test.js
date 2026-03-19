"use strict";

import { checkTestFunctionInFile, checkTestFunctionError, checkTestFunctionInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- type decl of strings w/o constraints", () => {
    it("should check string options type decl", function () {
        checkTestFunctionInFile('type SV1 = String; function main(): SV1 { return "ok"<SV1>; }');  
        checkTestFunctionInFile("type SV2 = CString; function main(): SV2 { return 'ok'<SV2>; }");  
    });

    it("should fail not string", function () {
        checkTestFunctionError('type SV1 = String; function main(): SV1 { return 3n<SV1>; }', "Literal value is not the same type (Nat) as the value type (String)");
    });

    it("should fail not type", function () {
        checkTestFunctionError('type SV1 = String; function main(): Int { return "ok"<SV1>; }', "Expected a return value of type Int but got SV1");
    });
});

describe ("Checker -- type decl of strings w/ size constraints", () => {
    it("should check string options type decl", function () {
        checkTestFunctionInFile('type SV1 = String{1n, 3n}; function main(): SV1 { return "abc"<SV1>; }');  
        checkTestFunctionInFile("const re2: CRegex = /[0-9]+/c; type SV2 = CString{1n} of Main::re2; function main(): SV2 { return '3'<SV2>; }");  
        checkTestFunctionInFile("const re2: CRegex = /[0-9]+/c; type SV2 = CString{3n, } of Main::re2; function main(): SV2 { return '345'<SV2>; }");  
        checkTestFunctionInFile("const re2: CRegex = /[0-9]+/c; type SV2 = CString{, 3n} of Main::re2; function main(): SV2 { return '3'<SV2>; }");  
    });

    it("should fail range index types", function () {
        checkTestFunctionInFileError('type SV1 = String{, }; function main(): SV1 { return "abc"<SV1>; }', "Invalid size range max and min -- at least one must be defined");  
        checkTestFunctionInFileError('type SV1 = String{3n, 1n}; function main(): SV1 { return "abc"<SV1>; }', "String literal length 3 out of bounds");  
    });

    it("should fail range limits", function () {
        checkTestFunctionInFileError('type SV1 = String{1n, 3n}; function main(): SV1 { return ""<SV1>; }', "String literal length 0 out of bounds");
        checkTestFunctionInFileError('type SV1 = String{1n, 3n}; function main(): SV1 { return "aaaa"<SV1>; }', "String literal length 4 out of bounds");

        checkTestFunctionInFileError("const re2: CRegex = /[0-9]+/c; type SV2 = CString{1n} of Main::re2; function main(): SV2 { return '34'<SV2>; }", "CString literal length 2 out of bounds");
        checkTestFunctionInFileError("const re2: CRegex = /[0-9]+/c; type SV2 = CString{1n} of Main::re2; function main(): SV2 { return ''<SV2>; }", "CString literal length 0 out of bounds");  

        checkTestFunctionInFileError("const re2: CRegex = /[0-9]+/c; type SV2 = CString{3n, } of Main::re2; function main(): SV2 { return '34'<SV2>; }", "CString literal length 2 out of bounds");  
        checkTestFunctionInFileError("const re2: CRegex = /[0-9]+/c; type SV2 = CString{, 3n} of Main::re2; function main(): SV2 { return '3457'<SV2>; }", "CString literal length 4 out of bounds");  
    });
});

describe ("Checker -- type decl of strings w/ regex constraints", () => {
    it("should check string options type decl", function () {
        checkTestFunctionInFile('type SV1 = String of /[a-z]+/; function main(): SV1 { return "abc"<SV1>; }');  
        checkTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; function main(): SV2 { return '3'<SV2>; }");  
    });

    it("should fail type mismatch", function () {
        checkTestFunctionError('type SV1 = CString of /[a-z]+/c; function main(): SV1 { return "ab3"<SV1>; }', "Typed string literal type must have base type String -- SV1");  
        checkTestFunctionError("const re2: Regex = /[0-9]/; type SV2 = CString of Main::re2; function main(): SV2 { return '345'<SV2>; }", "Unable to resolve cregex validator");  
    });

    it("should fail string constraints", function () {
        checkTestFunctionError('type SV1 = String of /[a-z]+/; function main(): SV1 { return "ab3"<SV1>; }', 'Literal value "ab3" does not match regex -- /[a-z]+/');  
        checkTestFunctionError("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; function main(): SV2 { return '345'<SV2>; }", 'Literal value "345" does not match regex -- /[0-9]/c');  
    });
});

describe ("Checker -- type decl of strings w/ both regex and size constraints", () => {
    it("should check string options type decl", function () {
        checkTestFunctionInFile('type SV1 = String{1n, 3n} of /[a-z]+/; function main(): SV1 { return "abc"<SV1>; }');  
        checkTestFunctionInFile("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; function main(): SV2 { return '3'<SV2>; }");  
    });
});

describe ("Checker -- type decl zipcode/css", () => {
    it("should check string options type decl", function () {
        checkTestFunctionInFile('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; function main(): Zipcode { return "98052-0000"<Zipcode>; }');
        checkTestFunctionInFile('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; function main(): Zipcode { return "40502"<Zipcode>; }');

        checkTestFunctionInFile('type CSSPt = String of /[0-9]+"pt"/; function main(): CSSPt { return "3pt"<CSSPt>; }');
    });

    it("should fail string constraints", function () {
        checkTestFunctionError('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; function main(): Zipcode { return "1234"<Zipcode>; }', 'Literal value "1234" does not match regex -- /[0-9]{5}("-"[0-9]{4})?/');  
        checkTestFunctionError('type CSSPt = String of /[0-9]+"pt"/; function main(): CSSPt { return "3px"<CSSPt>; }', 'Literal value "3px" does not match regex -- /[0-9]+"pt"/');  
    });

    it("should fail type mismatch", function () {
        checkTestFunctionError('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; type CSSPt = String of /[0-9]+"pt"/; function main(): CSSPt { return "87111"<Zipcode>; }', "Expected a return value of type CSSPt but got Zipcode");  
    });
});
