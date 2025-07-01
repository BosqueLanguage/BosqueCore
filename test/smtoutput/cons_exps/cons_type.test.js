"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";


describe ("SMT -- Type Alias Constructor", () => {
    it("should smt exec positional", function () {
        runishMainCodeUnsat('type Foo = Int; public function main(): Int { return Foo{1i}.value; }', "(assert (not (= 1 Main@main)))");
    });
});


describe ("SMT -- Type Alias w/ Invariant Constructor", () => {
    it("should smt exec positional", function () {
        runishMainCodeUnsat('type Foo = Int & { invariant $value > 3i; } public function main(): Int { return Foo{4i}.value; }', "(assert (not (= (@Result-ok 4) Main@main)))");
    });

    it("should smt fail inv", function () {
        runishMainCodeUnsat("type Foo = Int & { invariant $value > 3i; } public function main(): Int { return Foo{1i}.value; }", "(assert (not (is-@Result-err Main@main)))");
    });
});

/*
describe ("SMT -- type decl of strings w/ constraints", () => {
    it("should exec string options type decl", function () {
        runMainCode('type SV2 = String of /[a-z]+ & [a-c]+/; public function main(): String { return SV2{"abc"}.value; }', '"abc"');
        runMainCode("type SV2 = CString of /[a-z]+ & [a-c]+/c; public function main(): CString { return SV2{'abc'}.value; }", "'abc'");

        runMainCode('const re2: Regex = /[a-z]+/; type SV2 = String of /${Main::re2} & [a-c]+/; public function main(): String { return SV2{"abc"}.value; }', '"abc"');  
    });

    it("should fail string constraints", function () {
        runMainCodeError('type SV2 = String of /[a-z]+ & [az]+/; public function main(): String { return SV2{"abc"}.value; }', 'Error -- failed regex @ test.bsq:3'); 

        runMainCodeError('const re2: Regex = /[a-z]/; type SV2 = String of /${Main::re2} & [a-c]+/; public function main(): String { return SV2{"abc"}.value; }', "Error -- failed regex @ test.bsq:3");

        runMainCodeError("const re2: CRegex = /[a-c]/c; type SV1 = CString of Main::re2; public function main(): CString { return SV1{'abc'}.value; }", "Error -- failed regex -- re2['Main::re2'] @ test.bsq:3");
    });
});
*/