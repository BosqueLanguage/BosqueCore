"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- simple declare only", () => {
    it("should exec simple declares", function () {
        runTestSet("public function main(v: Int): Int { var x: Int; return 0i; }", [['3i', '0i']], []);
    });
});

describe ("CPPExec -- simple declare-assign only", () => {
    it("should exec simple declare-assign", function () {
        runTestSet("public function main(v: Int): Int { var x: Int = v; return x; }", [['3i', '3i']], []);
        runTestSet("public function main(v: Int): Int { ref x: Int = v; return x; }", [['3i', '3i']], []);
        runTestSet("public function main(b: Bool): Bool { let x: Bool = b; return x; }", [['true', 'true']], []);
    });

    it("should exec simple declare-assign infer type", function () {
        runTestSet("public function main(v: Int): Int { var x = v; return x; }", [['3i', '3i']], []);
        runTestSet("public function main(v: Int): Int { ref x = v; return x; }", [['3i', '3i']], []);
        runTestSet("public function main(b: Bool): Bool { let x = b; return x; }", [['true', 'true']], []);
    });

    it("should exec simple declare-assign with coerce (options)", function () {
        runTestSet('public function main(v: Int): Option<Int> { let x: Option<Int> = none; return x; }', [['0i', 'none']], []);
        runTestSet('public function main(v: Int): Option<Int> { let x: Option<Int> = some(v); return x; }', [['2i', 'some(2i)']], []);
        runTestSet('public function main(v: Int): Option<Int> { ref x: Option<Int> = some(v); return x; }', [['2i', 'some(2i)']], []);
    });

    it("should exec simple declare-assign with coerce (entity)", function () {
        runTestSet('concept Baz { field f: Int; } entity Foo provides Baz {} public function main(v: Int): Baz { let x: Baz = Foo{v}; return x; }', [['5i', 'Main::Foo{ 5i }']], []);
        runTestSet('concept Baz {} entity Foo provides Baz { field f: Int; } public function main(v: Int): Baz { var x: Baz = Foo{v}; return x; }', [['5i', 'Main::Foo{ 5i }']], []);

        runTestSet('concept Baz {} entity Foo provides Baz { field f: Int; } public function main(v: Foo): Baz { var x: Baz = v; return x; }', [['Main::Foo{ 5i }', 'Main::Foo{ 5i }']], []);
    });
});

describe ("CPPExec -- simple assign", () => {
    it("should exec simple assign", function () {
        runTestSet("public function main(v: Int): Int { var x: Int = 5i; x = v; return x; }", [['3i', '3i']], []);
        runTestSet("public function main(v: Int): Int { var x: Int = 5i; x = v; x = 0i; return x; }", [['3i', '0i']], []);
    });

    it("should ignore assign", function () {
        runTestSet("public function main(v: Int): Int { _ = 2i; return 0i; }", [['3i', '0i']], []);
    });

    it("should exec simple assign with coerce (option)", function () {
        runTestSet('public function main(v: Int): Option<Int> { var x: Option<Int> = none; x = some(v); return x; }', [['5i', 'some(5i)']], []);
    });

    it("should exec simple assign with coerce (entity)", function () {
        runTestSet('concept Baz {} entity Foo provides Baz { field f: Int; } public function main(v: Int): Baz { var x: Baz = Foo{v}; x = Foo{v}; return x; }', [['5i', 'Main::Foo{ 5i }']], []);
        runTestSet('concept Baz {} entity Foo provides Baz { field f: Int; field g: Int; } public function main(v: Foo): Baz { var x: Baz = Foo{1i, 2i}; x = v; return x; }', [['Main::Foo{ 5i, 10i }', 'Main::Foo{ 5i, 10i }']], []);
        runTestSet('concept Baz {} entity Foo provides Baz { field f: Int; field g: Int; } public function main(v: Baz): Baz { var x: Baz = Foo{1i, 2i}; x = v; return x; }', [['Main::Foo{ 5i, 10i }', 'Main::Foo{ 5i, 10i }']], []);
    });
});
