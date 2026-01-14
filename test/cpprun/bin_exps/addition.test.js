"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple addition", () => {
    it("should exec simple ops", function () {
        runTestSet("public function main(x: Nat): Nat { return 5n + x; }", [['0n', '5n'], ['1n', '6n']], ['4611686018427387900n']);
        runTestSet("public function main(x: Int): Int { return x + 2i; }", [['0i', '2i'], ['-1i', '1i'], ['3i', '5i'], ['-4611686018427387903i', '-4611686018427387901i']], ['4611686018427387903i']);
    });

    it("should exec type alias ops", function () {
        runTestSet("type Foo = Nat; public function main(x: Foo): Foo { return x + 2n<Foo>; }", [['0n<Main::Foo>', '2n<Main::Foo>'], ['3n<Main::Foo>', '5n<Main::Foo>']], ['4611686018427387900n<Main::Foo>']);
        runTestSet("type Foo = Int & { invariant $value != 2i; } public function main(x: Foo): Foo { return x + x; }", [['0i<Main::Foo>', '0i<Main::Foo>'], ['-2i<Main::Foo>', '-4i<Main::Foo>']], ['1i<Main::Foo>']);

        runTestSet("type Foo = ChkNat; public function main(x: Foo): Foo { return x + 2N<Foo>; }", [['0N<Main::Foo>', '2N<Main::Foo>'], ['3N<Main::Foo>', '5N<Main::Foo>'], ['ChkNat::npos<Main::Foo>', 'ChkNat::npos<Main::Foo>']], []);
    });
});
