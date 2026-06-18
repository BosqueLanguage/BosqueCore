"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- simple debug", () => {
    it("should emit simple debug", function () {
        checkTestEmitMainFunction("public function main(): Int { if(true) { _debug 5i; } return 1i; }", "Int Mainᕒmain() { { BSQ_diag_emitInt(std::cout, 5_i, true); std::cout << std::endl; } return 1_i; }");
        checkTestEmitMainFunction("entity Foo { field f: Int; }public function main(x: Foo): Int {  _debug x; return 1i; }", 'Int Mainᕒmain(MainᕒFoo x) { { BSQ_diag_emitMainᕒFoo(std::cout, x, true); std::cout << std::endl; } return 1_i; }');
    });
});
