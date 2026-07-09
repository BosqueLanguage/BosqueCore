"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- type decl of strings w/o constraints", () => {
    it("should emit string options type decl", function () {
        checkTestEmitMainFunction('type SV1 = String; public function main(): SV1 { return "ok"<SV1>; }', 'MainᕒSV1 Mainᕒmain() { return MainᕒSV1(U"ok"_us); }');  
        checkTestEmitMainFunction("type SV2 = CString; public function main(): SV2 { return 'ok'<SV2>; }", 'MainᕒSV2 Mainᕒmain() { return MainᕒSV2("ok"_cs); }');  
    });
});

describe ("CPPEmit -- type decl of strings w/ size constraints", () => {
    it("should emit string options type decl", function () {
        checkTestEmitMainFunction('type SV1 = String{1n, 3n}; public function main(): SV1 { return "abc"<SV1>; }', 'MainᕒSV1 Mainᕒmain() { return MainᕒSV1(U"abc"_us); }');  
        checkTestEmitMainFunction("const re2: CRegex = /[0-9]+/c; type SV2 = CString{1n} of Main::re2; public function main(): SV2 { return '3'<SV2>; }", 'MainᕒSV2 Mainᕒmain() { return MainᕒSV2("3"_cs); }');  
        checkTestEmitMainFunction("const re2: CRegex = /[0-9]+/c; type SV2 = CString{3n, } of Main::re2; public function main(): SV2 { return '345'<SV2>; }", 'MainᕒSV2 Mainᕒmain() { return MainᕒSV2("345"_cs); }');  
        checkTestEmitMainFunction("const re2: CRegex = /[0-9]+/c; type SV2 = CString{, 3n} of Main::re2; public function main(): SV2 { return '3'<SV2>; }", 'MainᕒSV2 Mainᕒmain() { return MainᕒSV2("3"_cs); }');  
    });
});

describe ("CPPEmit -- type decl of strings w/ regex constraints", () => {
    it("should emit string options type decl", function () {
        checkTestEmitMainFunction('type SV1 = String of /[a-z]+/; public function main(): SV1 { return "abc"<SV1>; }', 'MainᕒSV1 Mainᕒmain() { return MainᕒSV1(U"abc"_us); }');  
        checkTestEmitMainFunction("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; public function main(): SV2 { return '3'<SV2>; }", 'MainᕒSV2 Mainᕒmain() { return MainᕒSV2("3"_cs); }');  
    });
});

describe ("CPPEmit -- type decl of strings w/ both regex and size constraints", () => {
    it("should emit string options type decl", function () {
        checkTestEmitMainFunction('type SV1 = String{1n, 3n} of /[a-z]+/; public function main(): SV1 { return "abc"<SV1>; }', 'MainᕒSV1 Mainᕒmain() { return MainᕒSV1(U"abc"_us); }');  
        checkTestEmitMainFunction("const re2: CRegex = /[0-9]/c; type SV2 = CString of Main::re2; public function main(): SV2 { return '3'<SV2>; }", 'MainᕒSV2 Mainᕒmain() { return MainᕒSV2("3"_cs); }');  
    });
});

describe ("CPPEmit -- type decl zipcode/css", () => {
    it("should emit string options type decl", function () {
        checkTestEmitMainFunction("type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c; public function main(): Zipcode { return '98052-0000'<Zipcode>; }", 'MainᕒZipcode Mainᕒmain() { return MainᕒZipcode("98052-0000"_cs); }');
        checkTestEmitMainFunction("type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c; public function main(): Zipcode { return '40502'<Zipcode>; }", 'MainᕒZipcode Mainᕒmain() { return MainᕒZipcode("40502"_cs); }');

        checkTestEmitMainFunction("type CSSPt = CString of /[0-9]+'pt'/c; public function main(): CSSPt { return '3pt'<CSSPt>; }", 'MainᕒCSSPt Mainᕒmain() { return MainᕒCSSPt("3pt"_cs); }');
    });
});
