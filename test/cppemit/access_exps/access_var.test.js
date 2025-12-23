"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- access argument", () => {
    it("should emit simple arg var access", function () {
        checkTestEmitMainFunction("public function main(x: Int): Int { return x; }", "Int Mainᕒmain(Int x) { return x; }");
        checkTestEmitMainFunction("public function main(x: Int, y: Bool): Bool { return y; }", "Bool Mainᕒmain(Int x, Bool y) { return y; }");
    });
});

