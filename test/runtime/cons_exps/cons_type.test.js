"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- Type Alias Constructor", () => {
    it("should exec positional", function () {
        runMainCode('type Foo = Int; public function main(): Int { return Foo{1i}.value; }', [1n, "Int"]);
    });
});

describe ("Exec -- Type Alias w/ Invariant Constructor", () => {
    it("should exec positional", function () {
        runMainCode('type Foo = Int & { invariant $value > 3i; } public function main(): Int { return Foo{4i}.value; }', [4n, "Int"]);
    });

    it("should fail inv", function () {
        runMainCodeError("type Foo = Int & { invariant $value > 3i; } public function main(): Int { return Foo{1i}.value; }", "Error -- failed invariant @ test.bsq:3");
    });
});

describe ("Exec -- type decl of strings w/ stacked constraints", () => {
    it("should exec string options type decl", function () {
        runMainCode('type SV2 = String of /[a-z]+ & [a-c]+/; public function main(): String { return SV2{"abc"}.value; }', ["abc", "String"]);
        runMainCode("type SV2 = CString of /[a-z]+ & [a-c]+/c; public function main(): CString { return SV2{'abc'}.value; }", ["abc", "CString"]);

        runMainCode('const re2: Regex = /[a-z]+/; type SV2 = String of /${Main::re2} & [a-c]+/; public function main(): String { return SV2{"abc"}.value; }', ["abc", "String"]);  
    });

    it("should fail string constraints", function () {
        runMainCodeError('type SV2 = String of /[a-z]+ & [az]+/; public function main(): String { return SV2{"abc"}.value; }', 'Error -- failed regex @ test.bsq:3'); 

        runMainCodeError('const re2: Regex = /[a-z]/; type SV2 = String of /${Main::re2} & [a-c]+/; public function main(): String { return SV2{"abc"}.value; }', "Error -- failed regex @ test.bsq:3");

        runMainCodeError("const re2: CRegex = /[a-c]/c; type SV1 = CString of Main::re2; public function main(): CString { return SV1{'abc'}.value; }", "Error -- failed regex -- re2['Main::re2'] @ test.bsq:3");
    });
});
