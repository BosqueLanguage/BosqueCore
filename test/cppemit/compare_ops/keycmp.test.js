"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- basic KeyComparator equals/less", () => {
    it("should emit KeyComparator operations", function () {
        checkTestEmitMainFunction("public function main(): Bool { return KeyComparator::equal<Nat>(0n, 1n); }", "Bool Mainᕒmain() { return 0_n == 1_n; }");
        checkTestEmitMainFunction("public function main(): Bool { return KeyComparator::less<Nat>(0n, 1n); }", "Bool Mainᕒmain() { return 0_n < 1_n; }");

        checkTestEmitMainFunction("public function main(): Bool { return KeyComparator::equal<CString>('', 'ok'); }", 'Bool Mainᕒmain() { return ᐸRuntimeᐳ::XCString::smliteral("") == ᐸRuntimeᐳ::XCString::smliteral("ok"); }');
        checkTestEmitMainFunction("public function main(): Bool { return KeyComparator::less<CString>('ok', 'ok'); }", 'Bool Mainᕒmain() { return ᐸRuntimeᐳ::XCString::smliteral("ok") < ᐸRuntimeᐳ::XCString::smliteral("ok"); }');
    });
});

describe ("CPPEmit -- type alias KeyComparator equals/less", () => {
    it("should emit KeyComparator operations", function () {
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return KeyComparator::equal<Foo>(1i<Foo>, 1i<Foo>); }", "Bool Mainᕒmain() { return MainᕒFoo{1_i} == MainᕒFoo{1_i}; }");
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(0i<Foo>, 1i<Foo>); }", "Bool Mainᕒmain() { return MainᕒFoo{0_i} < MainᕒFoo{1_i}; }")
    });
});

describe ("CPPEmit -- enum KeyComparator equals/less", () => {
    it("should emit KeyComparator operations", function () {
        checkTestEmitMainFunction("enum Foo { f, g } public function main(): Bool { return KeyComparator::equal<Foo>(Foo#f, Foo#f); }", "Bool Mainᕒmain() { return MainᕒFoo::f == MainᕒFoo::f; }");
        checkTestEmitMainFunction("enum Foo { f, g } public function main(): Bool { return KeyComparator::less<Foo>(Foo#f, Foo#f); }", "Bool Mainᕒmain() { return MainᕒFoo::f < MainᕒFoo::f; }");
    });
});
