"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- entity is", () => {
    it("should exec postfix ? option", function () {
        runTestSet("public function main(x: Option<Int>): Bool { return x.?none; }", [['none', 'true'], ['some(3i)', 'false']], []);
        runTestSet("public function main(x: Option<Int>): Bool { return x.?some; }", [['some(3i)', 'true'], ['none', 'false']], []);

        runTestSet("public function main(x: Option<Int>): Bool { return x.?<None>; }", [['none', 'true'], ['some(3i)', 'false']], []);
        runTestSet("public function main(x: Option<Int>): Bool { return x.?<Some<Int>>; }", [['some(3i)', 'true'], ['none', 'false']], []);
    });

    it("should exec postfix ? types", function () {
        runTestSet("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Bool { return x.?<Foo>; }", [['Main::Foo{5i}', 'true']], []);
        runTestSet("concept Bar {} concept Baz provides Bar {} entity Foo provides Baz { field f: Int; } public function main(x: Bar): Bool { return x.?<Baz>; }", [['Main::Foo{5i}', 'true']], []);

        runTestSet("concept Bar {} concept Baz provides Bar {} entity Foo provides Baz { field f: Int; } entity Fuzz provides Bar { field f: Int; } public function main(x: Bar): Bool { return x.?<Baz>; }", [['Main::Foo{5i}', 'true'], ['Main::Fuzz{5i}', 'false']], []);
    });

    it("should exec postfix ? types ADT", function () {
        runTestSet('datatype Foo of F1 { } F2 { } ; public function main(x: Foo): Bool { return x.?<F1>; }', [['Main::F1{ }', 'true'], ['Main::F2{ }', 'false']], []);

        runTestSet('concept Bar { } datatype Foo provides Bar of F1 { } F2 { }; public function main(x: Bar): Bool { return x.?<F1>; }', [['Main::F1{ }', 'true'], ['Main::F2{ }', 'false']], []);
        runTestSet('concept Bar { } datatype Foo provides Bar of F1 { } F2 { }; public function main(x: Bar): Bool { return x.?<Foo>; }', [['Main::F1{ }', 'true'], ['Main::F2{ }', 'true']], []);
    });
});
