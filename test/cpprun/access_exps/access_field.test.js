"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- access field", () => {
    it("should exec simple field access", function () {
        runTestSet("entity Foo { field f: Int; } public function main(x: Foo): Int { return x.f; }", [['Main::Foo{3i}', '3i']], []);
        runTestSet("entity Bar { field h: Bool; } entity Foo { field f: Bar; } public function main(x: Foo): Bool { return x.f.h; }", [['Main::Foo{Main::Bar{true}}', 'true']], []);
    });

    it("should exec inherited field access", function () {
        runTestSet("concept Baz { field h: Bool; } entity Foo provides Baz { field f: Int; } public function main(x: Foo): Int { return x.f; }", [['Main::Foo{false, 3i}', '3i']], []);
        runTestSet("concept Baz { field h: Bool; } entity Foo provides Baz { field f: Int; } public function main(x: Foo): Bool { return x.h; }", [['Main::Foo{false, 3i}', 'false']], []);
        
        runTestSet("entity FIn { field f: Int; } concept Bar { field h: FIn; } entity Foo provides Bar { field f: Bool; } public function main(x: Foo): Int { return x.h.f; }", [['Main::Foo{Main::FIn{5i}, true}', '5i']], []);
        runTestSet("entity FIn { field f: Int; } concept Bar { field h: FIn; } entity Foo provides Bar { field f: Bool; } public function main(x: Bar): Int { return x.h.f; }", [['Main::Foo{Main::FIn{5i}, true}', '5i']], []);
    });
});
