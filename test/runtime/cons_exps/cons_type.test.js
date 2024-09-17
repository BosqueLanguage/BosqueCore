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
        runMainCode('type SV1 = String of /[a-z]+/; type SV2 = SV1 of /[a-c]+/; public function main(): String { return SV2{"abc"}.primitive; }', ["abc", "String"]);  
        runMainCode('type SV1 = String of /[a-z]+/; type SV2 = SV1 of /[a-c]+/; public function main(): String { return SV2{SV1{"abc"}}.primitive; }', ["abc", "String"]); 
        runMainCode('type SV1 = String of /[a-z]+/; type SV2 = SV1 of /[a-c]+/; public function main(): String { return SV2{"abc"<SV1>}.value.value; }', ["abc", "String"]);  

        runMainCode('const re2: Regex = /[a-z]+/; type SV1 = String of Main::re2; type SV2 = SV1 of /[a-c]+/; public function main(): String { return SV2{"abc"}.primitive; }', ["abc", "String"]);  

        runMainCode("type SV1 = CString of /[a-z]+/c; type SV2 = SV1 of /[a-c]+/c; public function main(): CString { return SV2{'abc'<SV1>}.value.value; }", ["abc", "CString"]);
    });

    it("should fail string constraints", function () {
        runMainCodeError('type SV1 = String of /[a-z]+/; type SV2 = SV1 of /[az]+/; public function main(): String { return SV2{"abc"}.primitive; }', 'Error -- failed regex @ test.bsq:3'); 
        runMainCodeError('type SV1 = String of /[a-z]+/; type SV2 = SV1 of /[az]+/; public function main(): String { return SV2{"abc"<SV1>}.primitive; }', 'Error -- failed regex @ test.bsq:3');

        runMainCodeError('const re2: Regex = /[a-z]/; type SV1 = String of Main::re2; type SV2 = SV1 of /[a-c]+/; public function main(): String { return SV2{"abc"}.primitive; }', "Error -- failed regex -- re2['Main::re2'] @ test.bsq:3");

        runMainCodeError("const re2: CRegex = /[a-z]/c; type SV1 = CString of Main::re2; type SV2 = SV1 of /[a-c]+/c; public function main(): CString { return SV2{'abc'}.primitive; }", "Error -- failed regex -- re2['Main::re2'] @ test.bsq:3");
    });
});
