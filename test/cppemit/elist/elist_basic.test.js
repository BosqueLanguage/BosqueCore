"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- elist decl and access", () => {
    it("should emit simple elist", function () {
        checkTestEmitMainFunction('public function main(): Int { return (|2i, true|).0; }', 'Int Mainᕒmain() { return std::get<0>(std::tuple<Int, Bool>{2_i, TRUE}); }'); 
        checkTestEmitMainFunction('public function main(): Bool { return (|2i, true|).1; }', 'Bool Mainᕒmain() { return std::get<1>(std::tuple<Int, Bool>{2_i, TRUE}); }'); 

        checkTestEmitMainFunction('public function main(): Bool { let x = (|2i, true|); return x.1; }', 'Bool Mainᕒmain() { std::tuple<Int, Bool> x = std::tuple<Int, Bool>{2_i, TRUE}; return std::get<1>(x); }'); 

        checkTestEmitMainFunction('public function main(): (|Int, Bool|) { return (|2i, true|); }', 'std::tuple<Int, Bool> Mainᕒmain() { return std::tuple<Int, Bool>{2_i, TRUE}; }'); 
        checkTestEmitMainFunction('public function main(x: (|Int, Bool|)): Int { return 1i + x.0; }', 'Int Mainᕒmain(const std::tuple<Int, Bool>& x) { Int tmp_0 = std::get<0>(x); ᐸRuntimeᐳ::XInt::checkOverflowAddition(1_i, tmp_0, "test.bsq", 2); return 1_i + tmp_0; }'); 
    });

    it("should emit option elist", function () {
        checkTestEmitMainFunction('public function main(): Int { let x: Option<(|Int, Bool|)> = some((|2i, true|)); return x.@some.0; }', 'Int Mainᕒmain() { OptionᐸᗑEListᐸIntᐪBoolᐳᐳ x = OptionᐸᗑEListᐸIntᐪBoolᐳᐳ{SomeᐸᗑEListᐸIntᐪBoolᐳᐳ{std::tuple<Int, Bool>{2_i, TRUE}}}; ᐸRuntimeᐳ::bsq_typeassert((bool)(!x.isNone()), "test.bsq", 2, "Type assertion failed", "Type assertion failed"); return std::get<0>(x.unwrap()); }'); 
    });

    it("should emit nesting", function () {
        checkTestEmitMainFunction('public function main(): (|Int, (|Bool, Bool|)|) { return (|2i, (|true, false|)|); }', 'std::tuple<Int, std::tuple<Bool, Bool>> Mainᕒmain() { return std::tuple<Int, std::tuple<Bool, Bool>>{2_i, std::tuple<Bool, Bool>{TRUE, FALSE}}; }'); 
        checkTestEmitMainFunction('entity Foo { field pp: (|Int, Bool|); } public function main(): Foo { return Foo{(|2i, false|)}; }', 'MainᕒFoo Mainᕒmain() { return MainᕒFoo{std::tuple<Int, Bool>{2_i, FALSE}}; }'); 
    });
});
