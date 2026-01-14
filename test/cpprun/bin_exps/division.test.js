"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple division", () => {
    it("should exec simple cases", function () {
        runTestSet("public function main(x: Nat): Nat { return 8n // x; }", [['4n', '2n'], ['1n', '8n']], ['0n']);
        runTestSet("public function main(x: Int): Int { return +2i // x; }", [['1i', '2i'], ['-2i', '-1i']], ['0i']);
    });

    it("should exec type alias ops", function () {
        runTestSet("type Foo = Nat; public function main(x: Foo): Foo { return x // 2n; }", [['0n<Main::Foo>', '0n<Main::Foo>'], ['4n<Main::Foo>', '2n<Main::Foo>']], []);
        runTestSet("type Foo = Int & { invariant $value != 2i; } public function main(x: Foo): Foo { return x // 2i; }", [['0i<Main::Foo>', '0i<Main::Foo>'], ['-4i<Main::Foo>', '-2i<Main::Foo>']], ['4i<Main::Foo>']);

        runTestSet("type Foo = ChkNat; public function main(x: Foo): ChkNat { return x // x; }", [['3N<Main::Foo>', '1N'], ['ChkNat::npos<Main::Foo>', 'ChkNat::npos']], ['0N<Main::Foo>']);
    });
});
