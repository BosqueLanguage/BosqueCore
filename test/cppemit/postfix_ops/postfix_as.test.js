"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- entity as", () => {
    it("should emit postfix @ option", function () {
        checkTestEmitMainFunction("public function main(x: Option<Int>): None { return x@none; }", 'None Mainᕒmain(OptionᐸIntᐳ x) { ᐸRuntimeᐳ::bsq_typeassert((bool)(x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return none; }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { return x@!none; }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { ᐸRuntimeᐳ::bsq_typeassert((bool)(!x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return x.unwrap(); }');

        checkTestEmitMainFunction("public function main(x: Option<Int>): Int { return x@some; }", 'Int Mainᕒmain(OptionᐸIntᐳ x) { ᐸRuntimeᐳ::bsq_typeassert((bool)(!x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return x.unwrap(); }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): None { return x@!some; }", 'None Mainᕒmain(OptionᐸIntᐳ x) { ᐸRuntimeᐳ::bsq_typeassert((bool)(x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return none; }');

        checkTestEmitMainFunction("entity Foo { field f: Option<Int>; } public function main(x: Int): Int { let y = Foo{some(x)}; return y.f@some; }", 'Int Mainᕒmain(Int x) { MainᕒFoo y = MainᕒFoo{OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{x})}; OptionᐸIntᐳ tmp_0 = y.f; ᐸRuntimeᐳ::bsq_typeassert((bool)(!tmp_0.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return tmp_0.unwrap(); }');

        checkTestEmitMainFunction("public function main(x: Option<Int>): Some<Int> { return x@<Some<Int>>; }", 'SomeᐸIntᐳ Mainᕒmain(OptionᐸIntᐳ x) { ᐸRuntimeᐳ::bsq_typeassert((bool)(!x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return x.asSome(); }');
        checkTestEmitMainFunction("public function main(x: Option<Int>): None { return x@!<Some<Int>>; }", 'None Mainᕒmain(OptionᐸIntᐳ x) { ᐸRuntimeᐳ::bsq_typeassert((bool)(x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return none; }');
    });

    it("should emit postfix @ types", function () {
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Foo { return x@<Foo>; }", 'aaa');
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Bar { return x@!<Foo>; }", 'bbb');

        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Foo): Foo { return x@<Foo>; }", 'ccc');
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Foo): Bar { return x@<Bar>; }", 'ddd');

        checkTestEmitMainFunction("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } public function main(x: Baz): Baz { return x@!<Foo>; }", 'eee');
        checkTestEmitMainFunction("concept Bar {} concept Baz {} entity Foo provides Bar { field f: Int; } public function main(x: Baz): Bar { return x@<Bar>; }", 'fff');

        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Foo { return x@<Foo>; }", 'ppp');
        checkTestEmitMainFunction("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Bar { return x@!<Foo>; }", 'qqq');

        checkTestEmitMainFunction("concept Bar {} concept Baz provides Bar {} entity Foo provides Baz { field f: Int; } public function main(x: Bar): Baz { return x@<Baz>; }", 'rrr');
    });

    it.skip("should check postfix @ types ADT", function () {
    });

    it.skip("should check postfix @ types ADT fail", function () {
    });
});
