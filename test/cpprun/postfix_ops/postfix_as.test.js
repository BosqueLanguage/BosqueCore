"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- entity as", () => {

    it("should exec postfix @ option", function () {
        runTestSet("public function main(x: Option<Int>): None { return x@none; }", [['none', 'none']], ['some(3i)']);
        runTestSet("public function main(x: Option<Int>): Int { return x@some; }", [['some(3i)', '3i']], ['none']);

        runTestSet("public function main(x: Option<Int>): None { return x@<None>; }", [['none', 'none']], ['some(3i)']);
        runTestSet("public function main(x: Option<Int>): Some<Int> { return x@<Some<Int>>; }", [['some(3i)', 'some(3i)']], ['none']);
    });

    it("should exec postfix @ types", function () {
        runTestSet("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Foo { return x@<Foo>; }", [['Main::Foo{ 3i }', 'Main::Foo{ 3i }']], []);
        runTestSet("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Foo): Foo { return x@<Foo>; }", [['Main::Foo{ 3i }', 'Main::Foo{ 3i }']], []);
        runTestSet("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Foo): Bar { return x@<Bar>; }", [['Main::Foo{ 3i }', 'Main::Foo{ 3i }']], []);
        
        runTestSet("concept Bar {} concept Baz provides Bar {} entity Foo provides Baz { field f: Int; } public function main(x: Bar): Baz { return x@<Baz>; }", [['Main::Foo{ 5i }', 'Main::Foo{ 5i }']], []);
        runTestSet("concept Bar {} concept Baz provides Bar {} entity Foo provides Baz { field f: Int; } public function main(x: Baz): Bar { return x@<Bar>; }", [['Main::Foo{ 5i }', 'Main::Foo{ 5i }']], []);

        runTestSet("concept Bar {} concept Baz provides Bar {} entity Foo provides Baz { field f: Int; } entity Fuzz provides Bar { field f: Int; } public function main(x: Bar): Baz { return x@<Baz>; }", [['Main::Foo{ 5i }', 'Main::Foo{ 5i }']], ['Main::Fuzz{ 5i }']);
    });

    it.skip("should exec postfix @ types ADT", function () {
    });

    it.skip("should exec postfix @ types ADT fail", function () {
    });
});
