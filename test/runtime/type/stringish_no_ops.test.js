"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- type decl of strings w/o constraints", () => {
    it("should exec string options type decl", function () {
        runMainCode('type SV1 = String; public function main(): String { return "ok"<SV1>.value; }', '"ok');  
        runMainCode("type SV2 = CString; public function main(): CString { return 'ok'<SV2>.value; }", "'ok'");  
    });
});

describe ("Exec -- type decl of strings w/ constraints", () => {
    it("should exec string options type decl", function () {
        runMainCode('type SV1 = String of /[a-z]+/; public function main(): String { return "abc"<SV1>.value; }', '"abc"');  
        runMainCode("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; public function main(): CString { return '3'<SV2>.value; }", "'3'");  
    });
});

describe ("Exec -- type decl of string with value", () => {
    it("should exec string type decls", function () {
        runMainCode('type SV1 = String; public function main(): String { let x = "ok"<SV1>; return x.value; }', '"ok"');    
    });
});

describe ("Exec -- type decl zipcode/css", () => {
    it("should exec string options type decl", function () {
        runMainCode('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; public function main(): String { return "98052-0000"<Zipcode>.value; }', '"98052-0000"');
        runMainCode('type Zipcode = String of /[0-9]{5}("-"[0-9]{4})?/; public function main(): String { return "40502"<Zipcode>.value; }', '"40502"');

        runMainCode('type CSSPt = String of /[0-9]+"pt"/; public function main(): String { return "3pt"<CSSPt>.value; }', '"3pt"');
    });
});
