"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- from operation", () => {
    it("should emit simple from Number", function () {
        checkTestEmitMainFunction('type Foo = Int; public function main(): Foo { return Foo::from(3i); }', 'MainᕒFoo Mainᕒmain() { return MainᕒFoo{3_i}; }'); 
        checkTestEmitMainFunction('type Foo = Int; type Bar = Int; public function main(x: Bar): Foo { return Foo::from(x); }', 'MainᕒFoo Mainᕒmain(MainᕒBar x) { return MainᕒFoo{x}; }'); 

        checkTestEmitMainFunction('type Foo = Int & { invariant $value > 0i; } public function main(): Foo { return Foo::from(3i); }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(3_i)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{3_i}; }'); 
    });

    it("should emit simple from CString", function () {
        checkTestEmitMainFunction("type Foo = CString; public function main(): Foo { return Foo::from('ok'); }", 'MainᕒFoo Mainᕒmain() { return MainᕒFoo{"ok"_cs}; }'); 
        checkTestEmitMainFunction("type Foo = CString; type Bar = CString; public function main(x: Bar): Foo { return Foo::from(x); }", 'MainᕒFoo Mainᕒmain(MainᕒBar x) { return MainᕒFoo{x}; }'); 

        checkTestEmitMainFunction("type Foo = CString of /[a-z]+/c; public function main(): Foo { return Foo::from('ok'); }", 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::XCString::checkFormat("ok"_cs, ᐸRuntimeᐳ::g_cregexs[0], "test.bsq", 2); return MainᕒFoo{"ok"_cs}; }'); 
        checkTestEmitMainFunction("type Foo = CString of /[0-9]{2}/c; type Bar = CString; public function main(x: Bar): Foo { return Foo::from(x); }", 'MainᕒFoo Mainᕒmain(MainᕒBar x) { ᐸRuntimeᐳ::XCString::checkFormat(x, ᐸRuntimeᐳ::g_cregexs[0], "test.bsq", 2); return MainᕒFoo{x}; }'); 
    });

    it("should emit simple from String", function () {
        checkTestEmitMainFunction('type Foo = String; public function main(): Foo { return Foo::from("ok"); }', 'MainᕒFoo Mainᕒmain() { return MainᕒFoo{U"ok"_us}; }'); 
        checkTestEmitMainFunction('type Foo = String; type Bar = String; public function main(x: Bar): Foo { return Foo::from(x); }', 'MainᕒFoo Mainᕒmain(MainᕒBar x) { return MainᕒFoo{x}; }'); 

        checkTestEmitMainFunction('type Foo = String of /[a-z]+/; public function main(): Foo { return Foo::from("ok"); }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::XString::checkFormat(U"ok"_us, ᐸRuntimeᐳ::g_regexs[0], "test.bsq", 2); return MainᕒFoo{U"ok"_us}; }'); 
        checkTestEmitMainFunction('type Foo = String of /[0-9]{2}/; type Bar = String; public function main(x: Bar): Foo { return Foo::from(x); }', 'MainᕒFoo Mainᕒmain(MainᕒBar x) { ᐸRuntimeᐳ::XString::checkFormat(x, ᐸRuntimeᐳ::g_regexs[0], "test.bsq", 2); return MainᕒFoo{x}; }'); 
    });
});
