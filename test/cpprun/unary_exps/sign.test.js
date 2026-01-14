"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Simple numeric sign", () => {
    it("should exec simple sign", function () {
        runTestSet("public function main(x: Int): Int { return -x; }", [['0i', '0i'], ['5i', '-5i'], ['-5i', '5i']], []);
        runTestSet("public function main(x: ChkInt): ChkInt { return -x; }", [['0I', '0I'], ['5I', '-5I'], ['-5I', '5I'], ['ChkInt::npos', 'ChkInt::npos']], []);
    });

    it("should exec type alias sign", function () {
        runTestSet("type Foo = Int; public function main(x: Foo): Foo { return -x; }", [['0i<Main::Foo>', '0i<Main::Foo>'], ['5i<Main::Foo>', '-5i<Main::Foo>'], ['-5i<Main::Foo>', '5i<Main::Foo>']], []);
        runTestSet("type Foo = ChkInt; public function main(x: Foo): Foo { return -x; }", [['0I<Main::Foo>', '0I<Main::Foo>'], ['5I<Main::Foo>', '-5I<Main::Foo>'], ['-5I<Main::Foo>', '5I<Main::Foo>']], []);
    });
});
