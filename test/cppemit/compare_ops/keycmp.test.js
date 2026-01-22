"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- basic KeyComparator equals/less", () => {
    it("should emit KeyComparator operations", function () {
        checkTestEmitMainFunction("public function main(): Bool { return KeyComparator::equal<Nat>(0n, 1n); }", "aaa");
        checkTestEmitMainFunction("public function main(): Bool { return KeyComparator::less<Nat>(0n, 1n); }", "ccc");

        checkTestEmitMainFunction("public function main(): Bool { return KeyComparator::equal<CString>('', 'ok'); }", "eee");
        checkTestEmitMainFunction("public function main(): Bool { return KeyComparator::less<CString>('ok', 'ok'); }", "ggg");
    });
});

describe ("CPPEmit -- type alias KeyComparator equals/less", () => {
    it("should emit KeyComparator operations", function () {
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return KeyComparator::equal<Foo>(1i<Foo>, 1i<Foo>); }", "ppp");
        checkTestEmitMainFunction("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(0i<Foo>, 1i<Foo>); }", "qqq")
    });
});

describe ("CPPEmit -- enum KeyComparator equals/less", () => {
    it("should emit KeyComparator operations", function () {
        checkTestEmitMainFunction("enum Foo { f, g } public function main(): Bool { return KeyComparator::equal<Foo>(Foo#f, Foo#f); }", "Bool Mainᕒmain() { return MainᕒFoo::f == MainᕒFoo::f; }");
        checkTestEmitMainFunction("enum Foo { f, g } public function main(): Bool { return KeyComparator::less<Foo>(Foo#f, Foo#f); }", "yyy");
    });
});
