"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- simple debug", () => {
    it("should emit simple debug", function () {
        checkTestEmitMainFunction("public function main(): Int { if(true) { _debug 5i; } return 1i; }", "ppp");
        checkTestEmitMainFunction("entity Foo { field f: Int; }public function main(x: Foo): Int {  _debug x; return 1i; }", "qqq");
    });
});
