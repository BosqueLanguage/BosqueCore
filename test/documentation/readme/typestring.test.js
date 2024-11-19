"use strict";

import { checkTestFunctionInFileError, runMainCode, runMainCodeError } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

const zipcode = 'type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/;';
const csspt = 'type CSSPt = String of /[0-9]+"pt"/; function is3pt(s1: CSSPt): Bool { return s1.value === "3pt"; }';

describe ("type decl zipcode/css", () => {
    it("should fail string constraints", function () {
        checkTestFunctionInFileError(`${zipcode} function main(): Zipcode { return "1234"<Zipcode>; }`, 'Literal value "1234" does not match regex -- /[0-9]{5}("-"[0-9]{4})?/');  
        checkTestFunctionInFileError(`${csspt} function main(): CSSPt { return "3px"<CSSPt>; }`, 'Literal value "3px" does not match regex -- /[0-9]+"pt"/');  
    });

    it("should fail call", function () {
        checkTestFunctionInFileError(`${csspt} function main(): Bool { return is3pt("12"); }`, 'Argument s1 expected type CSSPt but got String'); 
        checkTestFunctionInFileError(`${zipcode} ${csspt} function main(): Bool { return is3pt("98052"<Zipcode>); }`, 'Argument s1 expected type CSSPt but got Zipcode'); 
    });
});

describe ("Exec -- type decl zipcode/css", () => {
    it("should exec string options type decl", function () {
        runMainCode(`${zipcode} public function main(): String { return "98052-0000"<Zipcode>.value; }`, ["98052-0000", "String"]);
        
        runMainCode(`${csspt} public function main(): Bool { return is3pt("3pt"<CSSPt>); }`, [true, "Bool"]);
        runMainCode(`${csspt} public function main(): Bool { return is3pt("4pt"<CSSPt>); }`, [false, "Bool"]);
    });
});

