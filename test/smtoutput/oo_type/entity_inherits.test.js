"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- entity decl inherits", () => {
    it("should smt exec simple entity inherits fields", function () {
        runishMainCodeUnsat('concept Foo { field f: Int; } entity Bar provides Foo { } public function main(): Int { return Bar{3i}.f; }', "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat('concept Foo { field f: Int; } entity Bar provides Foo { field g: Bool; } public function main(): Bool { return Bar{3i, true}.g; }', "(assert (not Main@main))"); 
        runishMainCodeUnsat('concept Foo { field f: Int; } concept Baz { field g: Bool; } entity Bar provides Foo, Baz { } public function main(): Int { return Bar{3i, true}.f; }', "(assert (not (= 3 Main@main)))"); 

        runishMainCodeUnsat('concept Foo<T> { field f: T; } entity Bar<T> provides Foo<T> { } public function main(): Int { return Bar<Int>{3i}.f; }', "(assert (not (= 3 Main@main)))"); 
        runishMainCodeUnsat('concept Foo<U> { field f: U; } entity Bar<T> provides Foo<T> { } public function main(): Int { return Bar<Int>{3i}.f; }', "(assert (not (= 3 Main@main)))"); 
    });

    it("should smt exec simple entity inherits fields and invariants", function () {
        runishMainCodeUnsat('concept Foo { field f: Int; invariant $f > 0i; } entity Bar provides Foo { } public function main(): Int { return Bar{3i}.f; }', "(assert (not (= 3 Main@main)))");
        runishMainCodeUnsat('concept Foo { field f: Int; } entity Bar provides Foo { invariant $f > 0i; } public function main(): Int { return Bar{3i}.f; }', "(assert (not (= 3 Main@main)))");

        runishMainCodeUnsat('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f > 0i; } public function main(): Int { return Bar{3i}.f; }', "(assert (not (= 3 Main@main)))");
    });

     it("should smt exec simple entity inherits fields and invariants", function () {
        runishMainCodeUnsat('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f >= 0i; } public function main(): Int { return Bar{0i}.f; }', "(assert (not (= (@Result-ok 0) Main@main)))"); 
        runishMainCodeUnsat('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f >= 0i; } public function main(): Int { return Bar{1i}.f; }', "(assert (not (= (@Result-ok 1) Main@main)))"); 
    });

    it("should smt fail exec simple entity inherits fields and invariants", function () {
        runishMainCodeUnsat('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f > 0i; } public function main(): Int { return Bar{0i}.f; }', "(assert (not (is-@Result-err Main@main)))"); 
        runishMainCodeUnsat('concept Foo { field f: Int; invariant $f != 0i; } entity Bar provides Foo { invariant $f > 0i; } public function main(): Int { return Bar{-1i}.f; }', "(assert (not (is-@Result-err Main@main)))"); 
    });
});
