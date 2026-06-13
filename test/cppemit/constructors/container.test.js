"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Container Constructor (List)", () => {
    it("should emit simple list constructors", function () {
        checkTestEmitMainFunction("public function main(): List<Int> { return List<Int>{}; }", "ListᐸIntᐳ Mainᕒmain() { return ListᐸIntᐳ{}; }");
        checkTestEmitMainFunction("public function main(x: Int): List<Int> { return List<Int>{x}; }", "ListᐸIntᐳ Mainᕒmain(Int x) { return ListᐸIntᐳ({x}); }");
        checkTestEmitMainFunction("public function main(x: Int): List<Int> { return List<Int>{1i, x, 3i}; }", "ListᐸIntᐳ Mainᕒmain(Int x) { return ListᐸIntᐳ({1_i, x, 3_i}); }");
    
        checkTestEmitMainFunction("public function main(): List<CString> { let s = 'ok'; return List<CString>{'a', s}; }", 'ListᐸCStringᐳ Mainᕒmain() { CString s = "ok"_cs; return ListᐸCStringᐳ::mk({"a"_cs, s}); }');
        checkTestEmitMainFunction("public function main(): List<CString> { return List<CString>{'a', 'b', 'c'}; }", 'ListᐸCStringᐳ Mainᕒmain() { return ListᐸCStringᐳ::mk({"a"_cs, "b"_cs, "c"_cs}); }');
    });

    it.skip("should emit spread and mixed list constructors", function () {
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{...l}; }", "aaa");
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{...l, ...l}; }", "bbb");
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }", "zzzz");
    });
});
