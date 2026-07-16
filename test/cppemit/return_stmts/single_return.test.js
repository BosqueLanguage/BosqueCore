"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- simple return", () => {
    it("should emit simple returns", function () {
        checkTestEmitMainFunction('public function main(x: Int): Int { return x; }', 'Int Mainᕒmain(Int x) { return x; }');
        checkTestEmitMainFunction('entity Foo { field f: Int; } public function main(x: Foo): Foo { return x; }', 'MainᕒFoo Mainᕒmain(MainᕒFoo x) { return x; }');

        checkTestEmitMainFunction('public function main(x: Int): Bool { return x == 0i; }', 'Bool Mainᕒmain(Int x) { return x == 0_i; }');
    });

    it("should emit constructor returns", function () {
        checkTestEmitMainFunction('entity Foo { field f: Int; } public function main(): Foo { return Foo{3i}; }', 'MainᕒFoo Mainᕒmain() { return MainᕒFoo{3_i}; }');
        checkTestEmitMainFunction('entity Foo { field f: Int; invariant $f !== 0i; } public function main(): Foo { return Foo{3i}; }', 'MainᕒFoo Mainᕒmain() { ᐸRuntimeᐳ::bsq_invariant((bool)(MainᕒFooᐤinvariant_0(3_i)), "test.bsq", 2, nullptr, "Failed Invariant"); return MainᕒFoo{3_i}; }');
    });

    it("should emit direct returns", function () {
        checkTestEmitMainFunction('public function foo(x: Int): Int { return x + 1i; } public function main(): Int { return foo(3i); }', 'Int Mainᕒmain() { return Mainᕒfoo(3_i); }');
        checkTestEmitMainFunction('concept Baz {} entity Foo provides Baz { field f: Int; } public function foo(x: Int): Foo { return Foo{x + 1i}; } public function main(): Baz { return foo(3i); }', 'MainᕒBaz Mainᕒmain() { MainᕒFoo tmp_0 = Mainᕒfoo(3_i); return MainᕒBaz{tmp_0}; }');
    });

    it("should emit returns with special coerce", function () {
        checkTestEmitMainFunction('public function main(): Option<Int> { return none; }', 'OptionᐸIntᐳ Mainᕒmain() { return OptionᐸIntᐳ::none; }');
        checkTestEmitMainFunction('public function main(): Option<Int> { return some(3i); }', 'OptionᐸIntᐳ Mainᕒmain() { return OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; }');
        checkTestEmitMainFunction('public function main(): Option<Int> { let x: Option<Int> = some(3i); return x; }', 'OptionᐸIntᐳ Mainᕒmain() { OptionᐸIntᐳ x = OptionᐸIntᐳ{SomeᐸIntᐳ{3_i}}; return x; }');

        checkTestEmitMainFunction('concept Baz {} entity Foo provides Baz {} public function main(): Baz { return Foo{}; }', 'MainᕒBaz Mainᕒmain() { return MainᕒBaz{MainᕒFoo{}}; }');
        checkTestEmitMainFunction('concept Baz {} entity Foo provides Baz {} public function main(): Baz { let x: Foo = Foo{}; return x; }', 'MainᕒBaz Mainᕒmain() { MainᕒFoo x = MainᕒFoo{}; return MainᕒBaz{x}; }');
    });
});

describe ("CPPEmit -- return with refs", () => {
    it("should emit return with refs", function () {
        checkTestEmitMainFunction("function foo(out y: Int): Int { return 1i; } public function main(): Int { var y: Int; return foo(out y); }", 'Int Mainᕒmain() { Int y; Int tmp_0 = Mainᕒfooᙾref(y); return tmp_0; }');
        checkTestEmitMainFunction("entity Foo { ref method foo(): Int { return 1i; } } public function main(): Int { ref z = Foo{}; return ref z.foo(); }", 'Int Mainᕒmain() { MainᕒFoo z = MainᕒFoo{}; Int tmp_0 = MainᕒFooᑀfooᙾref(z); return tmp_0; }');
    });

    it("should emit return with out? passthrough", function () {
        checkTestEmitMainFunction("function bar(out? y: Int): Bool { y = 1i; return true; } function foo(out? y: Int): Bool { return bar(out? y); } public function main(): Int { var y: Int; if(foo(out? y) { return y; } else { return 0i; } }", 'Int Mainᕒmain() { Int y; Bool tmp_0 = Mainᕒfooᙾref(y); if(tmp_0) { return y; } else { return 0_i; } }');
    });
});
