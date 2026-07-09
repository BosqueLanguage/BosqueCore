"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple multiplication", () => {
    it("should exec simple ops", function () {
        runTestSet("public function main(x: Nat): Nat { return 2n * x; }", [['0n', '0n'], ['1n', '2n']], ['4611686018427387900n']);
        runTestSet("public function main(x: Int): Int { return -1i * x; }", [['0i', '0i'], ['1i', '-1i'], ['-3i', '3i'], ['4611686018427387903i', '-4611686018427387903i']], []);
    });

    it("should exec type alias ops", function () {
        runTestSet("type Foo = Nat; public function main(x: Foo): Foo { return x * 2n; }", [['0n<Main::Foo>', '0n<Main::Foo>'], ['3n<Main::Foo>', '6n<Main::Foo>']], ['4611686018427387900n<Main::Foo>']);
        runTestSet("type Foo = Int & { invariant $value != 2i; } public function main(x: Foo): Foo { return x * -2i; }", [['0i<Main::Foo>', '0i<Main::Foo>'], ['-3i<Main::Foo>', '6i<Main::Foo>']], ['-1i<Main::Foo>']);

        runTestSet("type Foo = ChkNat; public function main(x: Foo): Foo { return x * 2N; }", [['0N<Main::Foo>', '0N<Main::Foo>'], ['3N<Main::Foo>', '6N<Main::Foo>'], ['ChkNat::npos<Main::Foo>', 'ChkNat::npos<Main::Foo>']], []);
    });
});
