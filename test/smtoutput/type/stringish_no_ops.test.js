"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- type decl of strings w/o constraints", () => {
    it("should smt exec string options type decl", function () {
        runishMainCodeUnsat("type SV2 = CString; public function main(): CString { return 'ok'<SV2>.value; }", '(assert (not (= "ok" Main@main)))');
    });
});

describe ("SMT -- type decl of strings w/ constraints", () => {
    it("should smt exec string options type decl", function () {
        runishMainCodeUnsat("type SV1 = CString of /[a-z]+/c; public function main(): CString { return 'abc'<SV1>.value; }", '(assert (not (= "abc" Main@main)))');  
        runishMainCodeUnsat("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; public function main(): CString { return '3'<SV2>.value; }", '(assert (not (= "3" Main@main)))');  
    });
});

describe ("SMT -- type decl of string with value", () => {
    it("should smt exec string type decls", function () {
        runishMainCodeUnsat("type SV1 = CString; public function main(): CString { let x = 'ok'<SV1>; return x.value; }", '(assert (not (= "ok" Main@main)))');    
    });
});

describe ("SMT -- type decl zipcode/css", () => {
    it("should smt exec string options type decl", function () {
        runishMainCodeUnsat("type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c; public function main(): CString { return '98052-0000'<Zipcode>.value; }", '(assert (not (= "98052-0000" Main@main)))');
        runishMainCodeUnsat("type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c; public function main(): CString { return '40502'<Zipcode>.value; }", '(assert (not (= "40502" Main@main)))');

        runishMainCodeUnsat("type CSSPt = CString of /[0-9]+'pt'/c; public function main(): CString { return '3pt'<CSSPt>.value; }", '(assert (not (= "3pt" Main@main)))');
    });
});
