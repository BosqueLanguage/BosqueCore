"use strict";

import { runMainCode, runMainCodeError } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- entity is/as", () => {
    it("should exec simple entity is", function () {
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Bar>; }', [true, "Bool"]);
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Baz>; }', [true, "Bool"]); 
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Baz>; }', [false, "Bool"]); 
    });

    it("should exec simple entity as", function () {
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { return Bar{3i}@<Bar>.f; }', [3n, "Int"]);
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { let bb: Foo = Bar{3i}; return bb@<Bar>.f; }', [3n, "Int"]);

        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { return Bar{3i}@<Foo>.f; }', [3n, "Int"]); 
    });

    it("should fail exec simple entity as", function () {
        runMainCodeError('concept Foo { field f: Int; } concept Baz { field g: Int; } entity Bar provides Foo { } entity Goo provides Foo, Baz { } public function main(): Int { let bb: Foo = Bar{3i}; return bb@<Baz>.g; }', "Error -- expected subtytype of Main::Baz @ test.bsq:3"); 
    });
});
