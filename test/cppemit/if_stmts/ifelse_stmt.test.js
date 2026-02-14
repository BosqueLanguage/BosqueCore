"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- ElseIf Statement", () => {
    it("should emit simple else ifs (simplify)", function () {
        checkTestEmitMainFunction("public function main(): Int { if(true) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { return 3_i; }");
        checkTestEmitMainFunction("public function main(): Int { if(false) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { return 1_i; }");

        checkTestEmitMainFunction("public function main(): Int { if(true || false) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { return 3_i; }");
        checkTestEmitMainFunction("public function main(): Int { if(true && true) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { return 3_i; }");
    });

    it("should emit simple else ifs general", function () {
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b) { return 3i; } else { return 1i; } }", "Int Mainᕒmain(Bool b) { if(b) { return 3_i; } else { return 1_i; } }");
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b) { return 3i; } else { assert 4i < 5i; } return 1i; }", 'Int Mainᕒmain(Bool b) { if(b) { return 3_i; } else { ᐸRuntimeᐳ::bsq_assert((bool)(4_i < 5_i), "test.bsq", 2, nullptr, "Assertion Failed"); } return 1_i; }');

        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b && true) { return 3i; } else { return 1i; } }", "Int Mainᕒmain(Bool b) { if(b) { return 3_i; } else { return 1_i; } }");
        checkTestEmitMainFunction("public function main(b: Bool): Int { if(b || true) { return 3i; } else { return 1i; } }", "Int Mainᕒmain(Bool b) { return 3_i; }");
    });

    it("should check type alias else ifs", function () {
        checkTestEmitMainFunction("type Foo = Bool; public function main(): Int { if(true<Foo> || false<Foo>) { return 3i; } else { return 1i; } }", "Int Mainᕒmain() { if((MainᕒFoo{((MainᕒFoo{TRUE}.value) | (MainᕒFoo{FALSE}.value))}).value) { return 3_i; } else { return 1_i; } }");
        checkTestEmitMainFunction("type Foo = Bool; public function main(b: Foo): Int { if(b || !!b) { return 3i; } else { return 1i; } }", "Int Mainᕒmain(MainᕒFoo b) { if((MainᕒFoo{((b.value) | ((MainᕒFoo{(!((MainᕒFoo{(!(b.value))}).value))}).value))}).value) { return 3_i; } else { return 1_i; } }");
    });
});
