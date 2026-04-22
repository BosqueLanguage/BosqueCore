"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- If Statement", () => {
    it("should exec simple ifs general", function () {
        runTestSet("public function main(b: Bool): Int { if(b) { return 3i; } return 1i; }", [['true', '3i'], ['false', '1i']], []);
        runTestSet("public function main(b: Bool): Int { if(b && true) { return 3i; } return 1i; }", [['true', '3i'], ['false', '1i']], []);
    });

    it("should exec simple ifs scc", function () {
        runTestSet("public function main(b: Bool): Int { if(b) { return 3i; } abort; }", [['true', '3i']], ['false']);
        runTestSet("public function main(b: Bool): Int { if(b) { abort; } return 1i; }", [['false', '1i']], ['true']);
    });

    it("should exec type alias ifs", function () {
        runTestSet("type Foo = Bool; public function main(b: Foo): Int { if(b) { return 3i; } return 1i; }", [['true<Main::Foo>', '3i'], ['false<Main::Foo>', '1i']], []);
    });

    it("should exec ifs w/ single itest specials", function () {
        runTestSet("public function main(x: Option<Int>): Int { if (x)!none { return 1i; } return 3i; }", [['some(3i)', '1i'], ['none', '3i']], []);
        runTestSet("public function main(x: Option<Int>): Int { if ($z = x)@some { return $z; } return 3i; }", [['some(1i)', '1i'], ['none', '3i']], []);

        runTestSet("public function main(x: Option<Option<Int>>): Int { if (x.@some)@some { return $_; } return 3i; }", [['some(some(0i))', '0i'], ['some(none)', '3i']], ['none']);
    });

    it("should exec ifs w/ single itest types", function () {
        runTestSet("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if (x)!<Foo> { return 1i; } return 3i; }", [['Main::Foo{0i}', '3i']], []);
        runTestSet("concept Bar {} entity Foo provides Bar { field f: Int; } public function main(x: Bar): Int { if (x)@<Foo> { return $x.f; } return 3i; }", [['Main::Foo{0i}', '0i']], []);
    
        runTestSet("public function main(x: Option<Int>): Int { if ($y = x)@<Some<Int>> { return $y.value; } return 1i; }", [['some(0i)', '0i'], ['none', '1i']], []);
    });

    it.todo("should exec ifs w/ multi itest", function () {
    });

    it.todo("should exec ifs w/ passing params", function () {
    });
});
