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
    });
});

describe ("Exec -- type alias KeyComparator equals/less", () => {
    it("should exec KeyComparator operations", function () {
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::equal<Foo>(0i<Foo>, 1i<Foo>); }", [false, "Bool"]);
        runMainCode("type Foo = Int; public function main(): Bool { return KeyComparator::less<Foo>(0i<Foo>, 1i<Foo>); }", [true, "Bool"]);
    });
});