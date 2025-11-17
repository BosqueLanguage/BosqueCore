"use strict";

import { checkTestFunction, checkTestFunctionError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- type decl of strings w/o constraints", () => {
    it("should check string options type decl", function () {
        checkTestFunction('type SV1 = String; function main(): SV1 { return "ok"<SV1>; }');  
        checkTestFunction("type SV2 = CString; function main(): SV2 { return 'ok'<SV2>; }");  
    });

    it("should fail not string", function () {
        checkTestFunctionError('type SV1 = String; function main(): SV1 { return 3n<SV1>; }', "Literal value is not the same type (Nat) as the value type (String)");
    });

    it("should fail not type", function () {
        checkTestFunctionError('type SV1 = String; function main(): Int { return "ok"<SV1>; }', "Expected a return value of type Int but got SV1");
    });
});

describe ("Checker -- type decl of strings w/ constraints", () => {
    it("should check string options type decl", function () {
        checkTestFunction('type SV1 = String of /[a-z]+/; function main(): SV1 { return "abc"<SV1>; }');  
        checkTestFunction("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; function main(): SV2 { return '3'<SV2>; }");  
    });

    it("should fail type mismatch", function () {
        checkTestFunctionError('type SV1 = CString of /[a-z]+/c; function main(): SV1 { return "ab3"<SV1>; }', "Literal value is not the same type (String) as the value type (CString)");  
        checkTestFunctionError("const re2: Regex = /[0-9]/; type SV2 = CString of Main::re2; function main(): SV2 { return '345'<SV2>; }", "Unable to resolve cregex validator");  
    });

    it("should fail string constraints", function () {
        checkTestFunctionError('type SV1 = String of /[a-z]+/; function main(): SV1 { return "ab3"<SV1>; }', 'Literal value "ab3" does not match regex -- /[a-z]+/');  
        checkTestFunctionError("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; function main(): SV2 { return '345'<SV2>; }", 'Literal value "345" does not match regex -- /[0-9]/c');  
    });
});

describe ("Checker -- type decl of string with value", () => {
    it("should check string type decls", function () {
        checkTestFunction('type SV1 = String; function main(): String { let x = "ok"<SV1>; return x.value; }');    
    });

    it("should fail not string", function () {
        checkTestFunctionError('type SV1 = String; function main(): Int { let x = "ok"<SV1>; return x.value; }', "Expected a return value of type Int but got String");
    });
});

describe ("Checker -- type decl zipcode/css", () => {
    it("should check string options type decl", function () {
        checkTestFunction('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; function main(): Zipcode { return "98052-0000"<Zipcode>; }');
        checkTestFunction('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; function main(): Zipcode { return "40502"<Zipcode>; }');

        checkTestFunction('type CSSPt = String of /[0-9]+"pt"/; function main(): CSSPt { return "3pt"<CSSPt>; }');
    });

    it("should fail string constraints", function () {
        checkTestFunctionError('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; function main(): Zipcode { return "1234"<Zipcode>; }', 'Literal value "1234" does not match regex -- /[0-9]{5}("-"[0-9]{4})?/');  
        checkTestFunctionError('type CSSPt = String of /[0-9]+"pt"/; function main(): CSSPt { return "3px"<CSSPt>; }', 'Literal value "3px" does not match regex -- /[0-9]+"pt"/');  
    });

    it("should fail type mismatch", function () {
        checkTestFunctionError('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; type CSSPt = String of /[0-9]+"pt"/; function main(): CSSPt { return "87111"<Zipcode>; }', "Expected a return value of type CSSPt but got Zipcode");  
    });
});

describe ("Checker -- type decl of strings w/ stacked constraints", () => {
    it("should check string options type decl", function () {
        checkTestFunction('type SV2 = String of /[a-c]+ & [a-z]+/; function main(): SV2 { return "abc"<SV2>; }');  
        checkTestFunction('const re2: Regex = /[a-z]+/; type SV2 = String of /${Main::re2} & [a-c]+/; function main(): SV2 { return "abc"<SV2>; }');  
    });

    it("should fail type mismatch", function () {
        checkTestFunctionError('type SV2 = String of /[a-z]+/c; function main(): SV2 { return "abc"<SV2>; }', "Unable to resolve regex validator");  
    });

    it("should fail string constraints", function () {
        checkTestFunctionError('type SV2 = String of /[a-z]+ & [az]+/; function main(): SV2 { return "abc"<SV2>; }', 'Literal value "abc" does not match regex -- /[a-z]+ & [az]+/');  
    });
});