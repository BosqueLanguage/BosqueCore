"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- ref updates", () => {
    it("should emit ref updates direct", function () {
        checkTestEmitMainFunction('entity Foo { field x: Int; } public function main(x: Int): Int { var z = Foo{x}; ref z[x = 5i]; return z.x; }', 'aaaa');
        checkTestEmitMainFunction('entity Foo { field x: Int; } public function main(x: Int): Int { ref z = Foo{x}; ref z[x = 5i]; return z.x; }', 'bbb');

        checkTestEmitMainFunction('entity Foo { field x: Int; } public function main(x: Int): Int { ref z = Foo{x}; ref z[x = $x + 1i]; return z.x; }', 'ccc');

        checkTestEmitMainFunction('entity Foo { field x: Int; field y: Bool; } public function main(x: Int): Int { ref z = Foo{x, false}; ref z[x = 5i]; return z.x; }', 'ddd');
        checkTestEmitMainFunction('entity Foo { field x: Int; field y: Bool; } public function main(x: Int): Int { ref z = Foo{x, false}; ref z[y = true, x = 9i]; return z.x; }', 'eee');
    });

    it("should emit ref updates direct with inherits/template", function () {
        checkTestEmitMainFunction('concept Bar { field g: Bool; } entity Foo provides Bar { field x: Int; } public function main(x: Int): Int { var z = Foo{true, x}; ref z[x = 5i]; return z.x; }', 'lll');
        checkTestEmitMainFunction('concept Bar { field g: Bool; } entity Foo provides Bar { field x: Int; } public function main(x: Int): Bool { var z = Foo{true, x}; ref z[g = false]; return z.g; }', 'lllw');

        checkTestEmitMainFunction('entity Foo<T> { field x: T; } public function main(x: Int): Int { var z = Foo<Int>{x}; ref z[x = 5i]; return z.x; }', 'mmm');

        checkTestEmitMainFunction('concept Bar<T> { field g: T; } entity Foo { field x: Int; } public function main(x: Int): Int { var z = Foo<Bool>{true, x}; ref z[x = 5i]; return z.x; }', 'nnn');
        checkTestEmitMainFunction('concept Bar<T> { field g: T; } entity Foo<T> provides Bar<T> { field x: Int; } public function main(x: Int): Bool { var z = Foo<Bool>{true, x}; ref z[g = z.x == 0i]; return z.g; }', 'nnnw');
    });

    it("should emit ref updates direct with invariants", function () {
    });

    it("should emit ref updates as params", function () {
        checkTestEmitMainFunction('entity Foo { field x: Int; } public function main(ref z: Foo): Int { ref z[x = 5i]; return z.x; }', 'fff');
        checkTestEmitMainFunction('entity Foo { field x: Int; ref method f() { ref this[x = 0i]; return; } } public function main(): Int { ref z = Foo{3i}; ref z.f(); return z.x; }', 'ggg');

        //don't need return value for Void invokes
        checkTestEmitMainFunction('entity Foo { field x: Int; ref method f() { ref this[x = 0i]; } } public function main(): Int { ref z = Foo{3i}; ref z.f(); return z.x; }', 'hhh');
    });
});
