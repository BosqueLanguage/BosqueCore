"use strict";

import { runishMainCodeUnsat } from "../../../bin/test/smtoutput/smtemit_nf.js";
import { describe, it } from "node:test";

describe ("SMT -- entity is/as", () => {
    it("should smt exec simple entity is", function () {
        runishMainCodeUnsat('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Bar>; }', "(assert (not Main@main))");
        runishMainCodeUnsat('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Baz>; }', "(assert (not Main@main))"); 
        runishMainCodeUnsat('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Baz>; }', "(assert Main@main)"); 
    });

    it("should smt exec simple entity as", function () {
        runishMainCodeUnsat('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { return Bar{3i}@<Bar>.f; }', "(assert (not (= Main@main 3)))");
        runishMainCodeUnsat('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { let bb: Foo = Bar{3i}; return bb@<Bar>.f; }', "(assert (not (= Main@main (@Result-ok 3))))");

        runishMainCodeUnsat('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { return Bar{3i}@<Foo>.f; }', "(assert (not (= Main@main 3)))");
    });

    it("should smt exec (fail) simple entity as", function () {
        runishMainCodeUnsat('concept Foo { field f: Int; } concept Baz { field g: Int; } entity Bar provides Foo { } entity Goo provides Foo, Baz { } public function main(): Int { let bb: Foo = Bar{3i}; return bb@<Baz>.g; }', "(assert (not (is-@Result-err (@Result-ok 3))))");
    });
});
