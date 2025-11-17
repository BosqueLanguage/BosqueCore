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

describe ("SMT -- type decl of strings w/ constraints", () => {
    it("should smt exec string options type decl", function () {
        runishMainCodeUnsat("type SV2 = CString of /[a-z]+/c; public function main(): CString { return SV2{'abc'}.value; }", '(assert (not (= (@Result-ok "abc") Main@main)))');
    });

    it("should smt fail string constraints", function () {
        runishMainCodeUnsat("const re2: CRegex = /[a-c]/c; type SV1 = CString of Main::re2; public function main(): CString { return SV1{'abc'}.value; }", "(assert (not (is-@Result-err Main@main)))");
    });
});
