"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Container Constructor (List)", () => {
    it("should emit simple list constructors", function () {
        checkTestEmitMainFunction("public function main(): List<Int> { return List<Int>{}; }", "ListᐸIntᐳ Mainᕒmain() { return ListᐸIntᐳ{}; }");
        checkTestEmitMainFunction("public function main(x: Int): List<Int> { return List<Int>{x}; }", "ListᐸIntᐳ Mainᕒmain(Int x) { return ListᐸIntᐳ::mki({x}); }");
        checkTestEmitMainFunction("public function main(x: Int): List<Int> { return List<Int>{1i, x, 3i}; }", "ListᐸIntᐳ Mainᕒmain(Int x) { return ListᐸIntᐳ::mki({1_i, x, 3_i}); }");
    
        checkTestEmitMainFunction("public function main(): List<CString> { let s = 'ok'; return List<CString>{'a', s}; }", 'ListᐸCStringᐳ Mainᕒmain() { CString s = "ok"_cs; return ListᐸCStringᐳ::mki({"a"_cs, s}); }');
        checkTestEmitMainFunction("public function main(): List<CString> { return List<CString>{'a', 'b', 'c'}; }", 'ListᐸCStringᐳ Mainᕒmain() { return ListᐸCStringᐳ::mk({"a"_cs, "b"_cs, "c"_cs}); }');
    });

    it("should emit spread and mixed list constructors", function () {
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{...l}; }", "ListᐸIntᐳ Mainᕒmain(ListᐸIntᐳ l) { return l; }");
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{...l, ...l}; }", "ListᐸIntᐳ Mainᕒmain(ListᐸIntᐳ l) { return ListᐸIntᐳ{}.mk_mixed_append(l).mk_mixed_append(l); }");
        checkTestEmitMainFunction("public function main(l: List<Int>): List<Int> { return List<Int>{1i, ...l, 3i}; }", "ListᐸIntᐳ Mainᕒmain(ListᐸIntᐳ l) { return ListᐸIntᐳ{}.pushBack(1_i).mk_mixed_append(l).pushBack(3_i); }");
    });

    it("should emit simple map constructors", function () {
        checkTestEmitMainFunction("public function main(): Map<Int, Nat> { return Map<Int, Nat>{}; }", "MapᐸIntᐪNatᐳ Mainᕒmain() { return MapᐸIntᐪNatᐳ{}; }");
        checkTestEmitMainFunction("public function main(x: Int): Map<Int, Nat> { return Map<Int, Nat>{x => 2n}; }", "MapᐸIntᐪNatᐳ Mainᕒmain(Int x) { return MapᐸIntᐪNatᐳ::mk({MapEntryᐸIntᐪNatᐳ{x, 2_n}}); }");
        checkTestEmitMainFunction("public function main(x: MapEntry<Int, Nat>): Map<Int, Nat> { return Map<Int, Nat>{1i => 2n, x}; }", "MapᐸIntᐪNatᐳ Mainᕒmain(MapEntryᐸIntᐪNatᐳ x) { return MapᐸIntᐪNatᐳ::mk({MapEntryᐸIntᐪNatᐳ{1_i, 2_n}, x}); }");
    
        checkTestEmitMainFunction("public function main(): Map<CString, Nat> { return Map<CString, Nat>{'a' => 1n, 'b' => 2n, 'c' => 3n}; }", 'MapᐸCStringᐪNatᐳ Mainᕒmain() { return MapᐸCStringᐪNatᐳ::mk({MapEntryᐸCStringᐪNatᐳ{"a"_cs, 1_n}, MapEntryᐸCStringᐪNatᐳ{"b"_cs, 2_n}, MapEntryᐸCStringᐪNatᐳ{"c"_cs, 3_n}}); }');
    });

    it.skip("should emit spread and mixed map constructors", function () {
    });

    it("should emit simple set constructors", function () {
        checkTestEmitMainFunction("public function main(): Set<Int> { return Set<Int>{}; }", "SetᐸIntᐳ Mainᕒmain() { return SetᐸIntᐳ{}; }");
        checkTestEmitMainFunction("public function main(x: Int): Set<Int> { return Set<Int>{x}; }", "SetᐸIntᐳ Mainᕒmain(Int x) { return SetᐸIntᐳ::mk({x}); }");
        checkTestEmitMainFunction("public function main(x: Int): Set<Int> { return Set<Int>{1i, x}; }", "SetᐸIntᐳ Mainᕒmain(Int x) { return SetᐸIntᐳ::mk({1_i, x}); }");
    
        checkTestEmitMainFunction("public function main(): Set<CString> { return Set<CString>{'a', 'b', 'c'}; }", 'SetᐸCStringᐳ Mainᕒmain() { return SetᐸCStringᐳ::mk({"a"_cs, "b"_cs, "c"_cs}); }');
    });

    it.skip("should emit spread and mixed set constructors", function () {
    });
});
