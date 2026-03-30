"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- entity is", () => {
    it("should emit postfix ? option", function () {
        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?none; }", "Bool Mainᕒmain(OptionᐸIntᐳ x) { return x.isNone(); }");
        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?!none; }", "Bool Mainᕒmain(OptionᐸIntᐳ x) { return !x.isNone(); }");

        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?some; }", "Bool Mainᕒmain(OptionᐸIntᐳ x) { return !x.isNone(); }");
        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?!some; }", "Bool Mainᕒmain(OptionᐸIntᐳ x) { return x.isNone(); }");

        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?<None>; }", "Bool Mainᕒmain(OptionᐸIntᐳ x) { return x.isNone(); }");
        checkTestEmitMainFunction("public function main(x: Option<Int>): Bool { return x?<Some<Int>>; }", "Bool Mainᕒmain(OptionᐸIntᐳ x) { return !x.isNone(); }");
    });

    it("should check postfix ? types", function () {
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Bool { return x?<Foo>; }", "Bool Mainᕒmain(MainᕒBar x) { return x.uval.isTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo); }");
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Bool { return x?!<Foo>; }", "Bool Mainᕒmain(MainᕒBar x) { return x.uval.isNotTypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo); }");

        checkTestEmitMainFunction("concept Bar {} concept Baz provides Bar {} entity Foo provides Baz { field f: Int; } public function main(x: Bar): Bool { return x?<Baz>; }", "Bool Mainᕒmain(MainᕒBar x) { return x.uval.isSubtypeOf(&ᐸRuntimeᐳ::g_typeinfo_MainᕒBaz); }");
    });

    it.skip("should check postfix ? types ADT", function () {
    });

    it.skip("should check postfix ? types ADT fail", function () {
    });
});
