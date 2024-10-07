"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- basic KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runMainCode("public function main(): Bool { return KeyComparator::equal<Nat>(0n, 1n); }", [false, "Bool"]);
        runMainCode("public function main(): Bool { return KeyComparator::equal<Nat>(1n, 1n); }", [true, "Bool"]);

        runMainCode("public function main(): Bool { return KeyComparator::less<Nat>(0n, 1n); }", [true, "Bool"]);
        runMainCode("public function main(): Bool { return KeyComparator::less<Nat>(1n, 1n); }", [false, "Bool"]);

        runMainCode("public function main(): Bool { return KeyComparator::equal<CString>('', 'ok'); }", [false, "Bool"]);
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('', 'ok'); }", [true, "Bool"]);
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('ok', 'ok'); }", [false, "Bool"]);

        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('oj', 'ok'); }", [true, "Bool"]);
        runMainCode("public function main(): Bool { return KeyComparator::less<CString>('on', 'ok'); }", [false, "Bool"]);
    });
});

describe ("Exec -- type alias KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::equal<Foo>(1i<Foo>, 1i<Foo>); }", [true, "Bool"]);
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::equal<Foo>(0i<Foo>, 1i<Foo>); }", [false, "Bool"]);

        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(0i<Foo>, 1i<Foo>); }", [true, "Bool"]);
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(1i<Foo>, 1i<Foo>); }", [false, "Bool"]);
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(2i<Foo>, 1i<Foo>); }", [false, "Bool"]);
    });
});

describe ("Exec -- enum KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runMainCode("enum Foo { f, g } public function main(): Bool { return KeyComparator::equal<Foo>(Foo#f, Foo#f); }", [true, "Bool"]);
        runMainCode("enum Foo { f, g } public function main(): Bool { return KeyComparator::equal<Foo>(Foo#f, Foo#g); }", [false, "Bool"]);

        runMainCode("enum Foo { f, g } public function main(): Bool { return KeyComparator::less<Foo>(Foo#f, Foo#f); }", [false, "Bool"]);
        runMainCode("enum Foo { f, g } public function main(): Bool { return KeyComparator::less<Foo>(Foo#f, Foo#g); }", [true, "Bool"]);
    });
});