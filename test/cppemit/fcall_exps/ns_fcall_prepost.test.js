"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- NamespaceFunction Pre/Post", () => {
    it("should emit simple positional", function () {
        checkTestEmitMainFunction("function foo(x: Int): Int requires x > 0i; { return 1i; } public function main(): Int { return foo(5i); }", 'Int Mainᕒmain() { ᐸRuntimeᐳ::bsq_requires((bool)(Mainᕒfooᐤrequires_0(5_i)), "test.bsq", 2, nullptr, "Failed Requires"); return Mainᕒfoo(5_i); }');
        checkTestEmitMainFunction("function foo(x: Int): Int ensures $return > 0i; { return 1i; } public function main(): Int { return foo(5i); }", 'Int Mainᕒmain() { Int tmp_0 = Mainᕒfoo(5_i); ᐸRuntimeᐳ::bsq_ensures((bool)(Mainᕒfooᐤensures_0(tmp_0, 5_i)), "test.bsq", 2, nullptr, "Failed Ensures"); return tmp_0; }');
    });
});
