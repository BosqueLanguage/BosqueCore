"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- elist decl and access", () => {
    it("should emit simple elist", function () {
        checkTestEmitMainFunction('public function main(): Int { return (|2i, true|).0; }', 'Int Mainᕒmain() { return (ᐸRuntimeᐳ::EList2<Int, Bool>{2_i, TRUE}).at<0, Int>(); }'); 
        checkTestEmitMainFunction('public function main(): Bool { return (|2i, true|).1; }', 'Bool Mainᕒmain() { return (ᐸRuntimeᐳ::EList2<Int, Bool>{2_i, TRUE}).at<1, Bool>(); }'); 

        checkTestEmitMainFunction('public function main(): Bool { let x = (|2i, true|); return x.1; }', 'Bool Mainᕒmain() { ᐸRuntimeᐳ::EList2<Int, Bool> x = ᐸRuntimeᐳ::EList2<Int, Bool>{2_i, TRUE}; return x.at<1, Bool>(); }'); 

        checkTestEmitMainFunction('public function main(): (|Int, Bool|) { return (|2i, true|); }', 'ᐸRuntimeᐳ::EList2<Int, Bool> Mainᕒmain() { return ᐸRuntimeᐳ::EList2<Int, Bool>{2_i, TRUE}; }'); 
        checkTestEmitMainFunction('public function main(x: (|Int, Bool|)): Int { return 1i + x.0; }', 'Int Mainᕒmain(const ᐸRuntimeᐳ::EList2<Int, Bool>& x) { Int tmp_0 = x.at<0, Int>(); ᐸRuntimeᐳ::XInt::checkOverflowAddition(1_i, tmp_0, "test.bsq", 2); return 1_i + tmp_0; }'); 
    });

    it("should emit option elist", function () {
        checkTestEmitMainFunction('public function main(): Int { let x: Option<(|Int, Bool|)> = some((|2i, true|)); return x.@some.0; }', 'Int Mainᕒmain() { OptionᐸᗑEListᐸIntᐪBoolᐳᐳ x = OptionᐸᗑEListᐸIntᐪBoolᐳᐳ{SomeᐸᗑEListᐸIntᐪBoolᐳᐳ{ᐸRuntimeᐳ::EList2<Int, Bool>{2_i, TRUE}}}; ᐸRuntimeᐳ::bsq_typeassert((bool)(!x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return (x.unwrap()).at<0, Int>(); }'); 
    });

    it("should emit nesting", function () {
        checkTestEmitMainFunction('public function main(): (|Int, (|Bool, Bool|)|) { return (|2i, (|true, false|)|); }', 'ᐸRuntimeᐳ::EList2<Int, ᐸRuntimeᐳ::EList2<Bool, Bool>> Mainᕒmain() { return ᐸRuntimeᐳ::EList2<Int, ᐸRuntimeᐳ::EList2<Bool, Bool>>{2_i, ᐸRuntimeᐳ::EList2<Bool, Bool>{TRUE, FALSE}}; }'); 
        checkTestEmitMainFunction('entity Foo { field pp: (|Int, Bool|); } public function main(): Foo { return Foo{(|2i, false|)}; }', 'MainᕒFoo* Mainᕒmain() { return ᐸRuntimeᐳ::MainᕒFoo_allocator.allocate(ᐸRuntimeᐳ::EList2<Int, Bool>{2_i, FALSE}); }'); 
    });
});
