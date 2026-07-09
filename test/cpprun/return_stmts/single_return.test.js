"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- simple return", () => {
    it("should exec simple returns", function () {
        runTestSet('public function main(x: Int): Int { return x; }', [['0i', '0i'], ['5i', '5i']], []);
        runTestSet('entity Foo { field f: Int; } public function main(x: Foo): Foo { return x; }', [['Main::Foo{ 0i }', 'Main::Foo{ 0i }'], ['Main::Foo{ 5i }', 'Main::Foo{ 5i }']], []);

        runTestSet('public function main(x: Int): Bool { return x == 0i; }', [['0i', 'true'], ['5i', 'false']], []);
    });

    it("should exec constructor returns", function () {
        runTestSet('entity Foo { field f: Int; } public function main(x: Int): Foo { return Foo{x}; }', [['0i', 'Main::Foo{ 0i }'], ['5i', 'Main::Foo{ 5i }']], []);
        runTestSet('entity Foo { field f: Int; invariant $f !== 0i; } public function main(x: Int): Foo { return Foo{x}; }', [['3i', 'Main::Foo{ 3i }']], ['0i']);
    });

    it("should exec direct returns", function () {
        runTestSet('public function foo(x: Int): Int { return x + 1i; } public function main(x: Int): Int { return foo(x); }', [['0i', '1i'], ['5i', '6i']], []);
        runTestSet('concept Baz {} entity Foo provides Baz { field f: Int; } public function foo(x: Int): Foo { return Foo{x + 1i}; } public function main(x: Int): Baz { return foo(x); }', [['0i', 'Main::Foo{ 1i }'], ['5i', 'Main::Foo{ 6i }']], []);
    });

    it("should exec returns with special coerce", function () {
        runTestSet('public function main(x: Int): Option<Int> { return none; }', [['3i', 'none']], []);

        runTestSet('public function main(v: Int): Option<Int> { return some(v); }', [['3i', 'some(3i)']], []);
        runTestSet('public function main(v: Int): Option<Int> { let x: Option<Int> = some(v); return x; }', [['3i', 'some(3i)']], []);

        runTestSet('concept Baz { field f: Int; } entity Foo provides Baz {} public function main(v: Int): Baz { return Foo{v}; }', [['0i', 'Main::Foo{ 0i }']], []);
        runTestSet('concept Baz {} entity Foo provides Baz {field f: Int; } public function main(v: Int): Baz { let x: Foo = Foo{v}; return x; }', [['3i', 'Main::Foo{ 3i }']], []);
    });
});
