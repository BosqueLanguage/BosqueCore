"use strict";

import { runMainCode } from "../../../bin/test/runtime/runtime_nf.js";
import { describe, it } from "node:test";

describe ("Exec -- entity is/as", () => {
    it("should exec simple entity is", function () {
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Bar>; }', "true");
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Baz>; }', "true"); 
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo { } public function main(): Bool { let bb: Foo = Bar{3i}; return bb?<Baz>; }', "false"); 
    });

    it("should exec simple entity as", function () {
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { return Bar{3i}@<Bar>.f; }', "3i");
        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { let bb: Foo = Bar{3i}; return bb@<Bar>.f; }', "3i");

        runMainCode('concept Foo { field f: Int; } concept Baz {} entity Bar provides Foo, Baz { } public function main(): Int { return Bar{3i}@<Foo>.f; }', "3i"); 
    });

/*
    it("should fail exec simple entity as", function () {
        runMainCodeError('concept Foo { field f: Int; } concept Baz { field g: Int; } entity Bar provides Foo { } entity Goo provides Foo, Baz { } public function main(): Int { let bb: Foo = Bar{3i}; return bb@<Baz>.g; }', "Error -- expected subtytype of Main::Baz @ test.bsq:3"); 
    });
*/
});
