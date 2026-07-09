"use strict";

import { checkTestFunctionError, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const zipcode = "type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c;";
const csspt = "type CSSPt = CString of /[0-9]+'pt'/c; function is3pt(s1: CSSPt): Bool { return s1.value === '3pt'; }";

describe ("type decl zipcode/css", () => {
    it("should fail string constraints", function () {
        checkTestFunctionError(`${zipcode} function main(): Zipcode { return '1234'<Zipcode>; }`, `Literal value "1234" does not match regex -- /[0-9]{5}('-'[0-9]{4})?/c`);  
        checkTestFunctionError(`${csspt} function main(): CSSPt { return '3px'<CSSPt>; }`, `Literal value "3px" does not match regex -- /[0-9]+'pt'/c`);  
    });

    it("should fail call", function () {
        checkTestFunctionError(`${csspt} function main(): Bool { return is3pt('12'); }`, 'Argument s1 expected type CSSPt but got CString'); 
        checkTestFunctionError(`${zipcode} ${csspt} function main(): Bool { return is3pt('98052'<Zipcode>); }`, 'Argument s1 expected type CSSPt but got Zipcode'); 
    });
});

describe ("Exec -- type decl zipcode/css", () => {
    it("should exec string options type decl", function () {
        runTestSet(`${zipcode} public function main(b: Bool): Zipcode { return '98052-0000'<Zipcode>; }`, [['true', "'98052-0000'<Main::Zipcode>"]], []);
        
        runTestSet(`${csspt} public function main(cv: CSSPt): Bool { return is3pt(cv); }`, [['"3pt"<Main::CSSPt>', 'true'], ['"4pt"<Main::CSSPt>', 'false']], []);
    });
});
