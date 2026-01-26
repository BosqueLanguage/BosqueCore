"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- If Statement", () => {
    it("should emit simple ifs (simplify)", function () {
        checkTestEmitMainFunction("public function main(): Int { if(true) { return 3i; } return 1i; }", "Int Mainᕒmain() { return 3_i; }");
        checkTestEmitMainFunction("public function main(): Int { if(false) { return 3i; } return 1i; }", "Int Mainᕒmain() { return 1_i; }");

        checkTestEmitMainFunction("public function main(): Int { if(true || false) { return 3i; } return 1i; }", "Int Mainᕒmain() { return 3_i; }");
        checkTestEmitMainFunction("public function main(): Int { if(true && true) { return 3i; } return 1i; }", "Int Mainᕒmain() { return 3_i; }");
    });

    it("should emit simple ifs general", function () {
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b) { return 3i; } return 1i; }", "Int Mainᕒmain(Bool b) { if(b) { return 3_i; } return 1_i; }");
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b && true) { return 3i; } return 1i; }", "Int Mainᕒmain(Bool b) { if(b) { return 3_i; } return 1_i; }");
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b || true) { return 3i; } return 1i; }", "Int Mainᕒmain(Bool b) { return 3_i; }");
    });

    it("should check type alias ifs", function () {
        checkTestEmitMainFunction("type Foo = Bool; public function main(): Int { if(true<Foo>) { return 3i; } return 1i; }", "Int Mainᕒmain() { if(MainᕒFoo{TRUE}.value) { return 3_i; } return 1_i; }");
        checkTestEmitMainFunction("type Foo = Bool; public function main(b: Foo): Int { if(b) { return 3i; } return 1i; }", "Int Mainᕒmain(MainᕒFoo b) { if(b.value) { return 3_i; } return 1_i; }");
    });
});
