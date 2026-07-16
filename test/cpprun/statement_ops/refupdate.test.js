"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- ref updates", () => {
    it("should exec ref updates direct", function () {
        runTestSet('entity Foo { field x: Int; } public function main(x: Int): Int { var z = Foo{x}; ref z[x = 5i]; return z.x; }', [['0i', '5i']], []);
        runTestSet('entity Foo { field x: Int; } public function main(x: Int): Int { var z = Foo{x}; var o = z; ref z[x = 5i]; return o.x; }', [['0i', '0i']], []);
        
        runTestSet('entity Foo { field x: Int; } public function main(x: Int): Int { ref z = Foo{x}; ref z[x = $x + 1i]; return z.x; }', [['0i', '1i']], []);

        runTestSet('entity Foo { field x: Int; field y: Bool; } public function main(x: Int): Int { ref z = Foo{x, false}; ref z[y = true, x = 9i]; return z.x; }', [['0i', '9i']], []);
    });

    it("should exec ref updates direct with inherits/template", function () {
        runTestSet('concept Bar { field g: Bool; } entity Foo provides Bar { field x: Int; } public function main(x: Int): Int { var z = Foo{true, x}; ref z[x = 5i]; return z.x; }', [['0i', '5i']], []);
        runTestSet('concept Bar { field g: Bool; } entity Foo provides Bar { field x: Int; } public function main(x: Int): Bool { var z = Foo{true, x}; ref z[g = false]; return z.g; }', [['0i', 'false']], []);

        runTestSet('entity Foo<T> { field x: T; } public function main(x: Int): Int { var z = Foo<Int>{x}; ref z[x = 5i]; return z.x; }', [['0i', '5i']], []);

        runTestSet('concept Bar<T> { field g: T; } entity Foo<T> provides Bar<T> { field x: Int; } public function main(x: Int): Int { var z = Foo<Bool>{true, x}; ref z[x = 5i]; return z.x; }', [['0i', '5i']], []);
        runTestSet('concept Bar<T> { field g: T; } entity Foo<T> provides Bar<T> { field x: Int; } public function main(x: Int): Bool { var z = Foo<Bool>{true, x}; ref z[g = z.x == 0i]; return z.g; }', [['0i', 'true'], ['1i', 'false']], []);
    });

    it("should exec ref updates direct with invariants", function () {
        runTestSet('entity Foo { field x: Int; invariant $x < 5i; } public function main(x: Int): Int { ref z = Foo{x}; ref z[x = $x + 1i]; return z.x; }', [['0i', '1i']], ['7i', '4i']);
        runTestSet('concept Bar { field g: Bool; invariant $g; } entity Foo provides Bar { field x: Int; } public function main(x: Int): Bool { var z = Foo{true, x}; ref z[g = z.x != 0i]; return z.g; }', [['1i', 'true']], ['0i']);
    });

    it("should exec ref updates as params", function () {
        runTestSet('entity Foo { field x: Int; } function f(ref z: Foo): Int { ref z[x = 5i]; return z.x; } public function main(k: Int): Int { ref z = Foo{3i}; return f(ref z); }', [['0i', '5i']], []);
        runTestSet('entity Foo { field x: Int; ref method f() { ref this[x = 0i]; } } public function main(k: Int): Int { ref z = Foo{3i}; ref z.f(); return z.x; }', [['0i', '0i']], []);
    });
});
