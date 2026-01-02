"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple subtraction", () => {
    it("should emit simple ops", function () {
        runTestSet("public function main(x: Nat): Nat { return 1n - x; }", [['1n', '0n'], ['0n', '1n']], ['5n']);
        runTestSet("public function main(x: Int): Int { return 2i - x; }", [['2i', '0i'], ['-1i', '3i'], ['0i', '2i']], []);
    });

    it("should exec type alias ops", function () {
        runTestSet("type Foo = Nat; public function main(x: Foo): Foo { return x - 2n<Foo>; }", [['2n<Main::Foo>', '0n<Main::Foo>'], ['3n<Main::Foo>', '1n<Main::Foo>']], ['1n<Main::Foo>']);
        runTestSet("type Foo = Int & { invariant $value != 2i; } public function main(x: Foo): Foo { return x - 5i<Foo>; }", [['0i<Main::Foo>', '-5i<Main::Foo>'], ['-2i<Main::Foo>', '-7i<Main::Foo>']], ['7i<Main::Foo>']);

        runTestSet("type Foo = ChkNat; public function main(x: Foo): Foo { return x - 2N<Foo>; }", [['2N<Main::Foo>', '0N<Main::Foo>'], ['3N<Main::Foo>', '1N<Main::Foo>'], ['ChkNat::npos<Main::Foo>', 'ChkNat::npos<Main::Foo>']], ['0N<Main::Foo>']);
    });
});
