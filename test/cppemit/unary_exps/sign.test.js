"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Simple numeric sign", () => {
    it("should emit (simplify) simple sign", function () {
        checkTestEmitMainFunction("public function main(): Int { return -(3i); }", "Int Mainᕒmain() { return -3_i; }");
        checkTestEmitMainFunction("public function main(): Nat { return +(5n); }", "Nat Mainᕒmain() { return 5_n; }");
    });

    it("should emit simple sign", function () {
        checkTestEmitMainFunction("public function main(x: Int): Int { return -x; }", "Int Mainᕒmain(Int x) { return -x; }");
        checkTestEmitMainFunction("public function main(x: Nat): Nat { return +x; }", "Nat Mainᕒmain(Nat x) { return x; }");
    });

    it("should emit type alias sign", function () {
        checkTestEmitMainFunction("type Foo = Int; public function main(x: Foo): Foo { return -x; }", "MainᕒFoo Mainᕒmain(MainᕒFoo x) { return MainᕒFoo{-(x.value)}; }");
        checkTestEmitMainFunction("type Foo = Nat; public function main(x: Foo): Foo { return +x; }", "MainᕒFoo Mainᕒmain(MainᕒFoo x) { return MainᕒFoo{x.value}; }");
        checkTestEmitMainFunction("type Foo = ChkInt; public function main(x: Foo): Foo { return -x; }", "MainᕒFoo Mainᕒmain(MainᕒFoo x) { return MainᕒFoo{-(x.value)}; }");
    });
});
