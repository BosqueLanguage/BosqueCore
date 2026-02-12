"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";


describe ("CPPExec -- Entity Constructor", () => {
    it("should exec positional", function () {
        runTestSet('entity Foo { field f: Int; } public function main(v: Int): Foo { return Foo{v}; }', [['3i', 'Main::Foo{ 3i }'], ['0i', 'Main::Foo{ 0i }']], []);
        runTestSet('entity Foo { field f: Int; field g: Bool; } public function main(v: Int): Foo { return Foo{v, v == 0i}; }', [['3i', 'Main::Foo{ 3i, false }'], ['0i', 'Main::Foo{ 0i, true }']], []);
    });

    it("should exec nominal", function () {
        runTestSet('entity Foo { field f: Int; } public function main(v: Int): Foo { return Foo{f = v + 1i}; }', [['1i', 'Main::Foo{ 2i }'], ['5i', 'Main::Foo{ 6i }']], []);
        runTestSet('entity Foo { field f: Int; field g: Bool; } public function main(b: Bool): Foo { return Foo{f = 1i, g = !b}; }', [['true', 'Main::Foo{ 1i, false }'], ['false', 'Main::Foo{ 1i, true }']], []);
    });

    it("should exec default", function () {
        runTestSet('entity Foo { field f: Int = 0i; } public function main(v: Int): Foo { return Foo{}; }', [['3i', 'Main::Foo{ 0i }']], []);
        runTestSet('entity Foo { field f: Int = 0i; } public function main(v: Int): Foo { return Foo{v}; }', [['3i', 'Main::Foo{ 3i }']], []);
    });

    it("should exec skip positions", function () {
        runTestSet('entity Foo { field f: Int; field g: Bool = true; field h: Int; } public function main(v: Int): Foo { return Foo{1i, _, h = v + v}; }', [['3i', 'Main::Foo{ 1i, true, 6i }']], []);
    });
});

describe ("CPPExec -- Entity w/ Invariant Constructor", () => {
    it("should exec positional", function () {
        runTestSet('entity Foo { field f: Int; invariant $f > 3i; } public function main(v: Int): Foo { return Foo{v}; }', [['4i', 'Main::Foo{ 4i }']], ['0i']);
        runTestSet('entity Foo { field f: Int; field g: Bool; invariant $g ==> $f > 3i; } public function main(v: Int): Foo { return Foo{v, true}; }', [['4i', 'Main::Foo{ 4i, true }']], ['1i']);

        runTestSet('entity Foo { field f: Int; field g: Bool; invariant !$g; invariant $f != 0i; } public function main(v: Int): Foo { return Foo{v, false}; }', [['1i', 'Main::Foo{ 1i, false }']], ['0i']);
    });

    it("should exec default", function () {
        runTestSet('entity Foo { field f: Int = 0i; invariant $f != 3i; } public function main(v: Int): Foo { return Foo{}; }', [['3i', 'Main::Foo{ 0i }']], []);
    });

    it.todo("should exec inherits single", function () {
    });

    it.todo("should exec inherits multiple", function () {
    });

    it.todo("should exec inherits with invariants too", function () {
    });
});
