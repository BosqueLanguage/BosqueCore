"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Container Constructor (List)", () => {
    it("should emit simple list constructors", function () {
        checkTestEmitMainFunction("public function main(): List<Int> { return List<Int>{}; }", "ListᐸIntᐳ Mainᕒmain() { return ListᐸIntᐳ{}; }");
        checkTestEmitMainFunction("public function main(x: Int): List<Int> { return List<Int>{x}; }", "ListᐸIntᐳ Mainᕒmain(Int x) { return ListᐸIntᐳ({x}); }");
        checkTestEmitMainFunction("public function main(x: Int): List<Int> { return List<Int>{1i, x, 3i}; }", "ListᐸIntᐳ Mainᕒmain(Int x) { return ListᐸIntᐳ({1_i, x, 3_i}); }");
    
        checkTestEmitMainFunction("public function main(): List<CString> { let s = 'ok'; return List<CString>{'a', s}; }", 'ListᐸCStringᐳ Mainᕒmain() { CString s = "ok"_cs; return ListᐸCStringᐳ({"a"_cs, s}); }');
        checkTestEmitMainFunction("public function main(): List<CString> { return List<CString>{'a', 'b', 'c'}; }", 'ListᐸCStringᐳ Mainᕒmain() { return ListᐸCStringᐳ::mk({"a"_cs, "b"_cs, "c"_cs}); }');
    });

    it.skip("should emit spread and mixed list constructors", function () {
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{...l}; }", "aaa");
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{...l, ...l}; }", "bbb");
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }", "zzzz");
    });

    it("should emit simple map constructors", function () {
        checkTestEmitMainFunction("public function main(): Map<Int, Nat> { return Map<Int, Nat>{}; }", "MapᐸIntᐪNatᐳ Mainᕒmain() { return MapᐸIntᐪNatᐳ{}; }");
        checkTestEmitMainFunction("public function main(x: Int): Map<Int, Nat> { return Map<Int, Nat>{x => 2n}; }", "MapᐸIntᐪNatᐳ Mainᕒmain(Int x) { return MapᐸIntᐪNatᐳ::mk({MapEntryᐸIntᐪNatᐳ{x, 2_n}}); }");
        checkTestEmitMainFunction("public function main(x: MapEntry<Int, Nat>): Map<Int, Nat> { return Map<Int, Nat>{1i => 2n, x}; }", "MapᐸIntᐪNatᐳ Mainᕒmain(MapEntryᐸIntᐪNatᐳ x) { return MapᐸIntᐪNatᐳ::mk({MapEntryᐸIntᐪNatᐳ{1_i, 2_n}, x}); }");
    
        checkTestEmitMainFunction("public function main(): Map<CString, Nat> { return Map<CString, Nat>{'a' => 1n, 'b' => 2n, 'c' => 3n}; }", 'MapᐸCStringᐪNatᐳ Mainᕒmain() { return MapᐸCStringᐪNatᐳ::mk({MapEntryᐸCStringᐪNatᐳ{"a"_cs, 1_n}, MapEntryᐸCStringᐪNatᐳ{"b"_cs, 2_n}, MapEntryᐸCStringᐪNatᐳ{"c"_cs, 3_n}}); }');
    });

    it.skip("should emit spread and mixed map constructors", function () {
    });
});
