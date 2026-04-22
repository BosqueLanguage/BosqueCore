"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- NamespaceFunction Ref Params", () => {
    it("should exec simple ref", function () {
        runTestSet('function foo(out y: Int): Int { y = 2i; return 1i; } public function main(): Int { var i = 0i; return foo(out i); }', [['1i', '1i']], []);
        runTestSet('function foo(out? y: Int): Bool { y = 2i; return true; } public function main(): Bool { var i = 0i; return foo(out? i); }', [['true', 'true']], []);
        runTestSet('function foo(inout y: Int): Int { y = y + 2i; return 1i; } public function main(): Int { var i = 0i; return foo(inout i); }', [['1i', '1i']], []);
        runTestSet('entity Foo{ } function foo(ref y: Foo): Int { return 1i; } public function main(): Int { ref ff = Foo{}; return foo(ref ff); }', [['1i', '1i']], []);
    });

    it("should exec staged ref", function () {
        runTestSet('function foo(out y: Int, x: Int): Int { y = 2i; return x; } public function main(v: Int): Int { var i = 0i; let z = foo(out i, v); return z + i; }', [['1i', '3i'], ['0i', '2i']], []);
        runTestSet('function foo(out y: Int): Int { y = 2i; return 1i; } public function main(v: Int): Int { var i = v; i = foo(out i); return i; }', [['2i', '1i']], []);
        runTestSet('function foo(inout y: Int): Int { y = y + 2i; return y; } public function main(v: Int): Int { var i = v; i = foo(inout i); return i; }', [['3i', '5i'], ['0i', '2i']], []);
        runTestSet('entity Foo{ } function foo(ref y: Foo) { return; } public function main(v: Int): Foo { ref ff = Foo{}; foo(ref ff); return ff; }', [['0i', 'Main::Foo{  }']], []);
        runTestSet('function foo(v: Int, out y: Int): Int { y = 2i; return v; } public function main(v: Int): Int { var i = 0i; let x = foo(v, out i); return x + i; }', [['2i', '4i'], ['0i', '2i']], []);
    });

    it("should exec simple out?", function () {
        runTestSet('function foo(v: Int, out? y: Int): Bool { if(v == 0i) { y = 2i; return true; } return false; } public function main(v: Int): Int { var i: Int; if(foo(v, out? i)) { return i + 1i; } return 0i; }', [['0i', '3i'], ['1i', '0i'], ['5i', '0i']], []);
    });
});
