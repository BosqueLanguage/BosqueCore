"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- ElseIf Statement", () => {
    it("should exec simple else ifs general", function () {
        runTestSet("public function main(b: Bool): Int { if(b) { return 3i; } else { return 1i; } }", [['true', '3i'], ['false', '1i']], []);
        runTestSet("public function main(b: Bool): Int { if(b && true) { return 3i; } else { return 1i; } }", [['true', '3i'], ['false', '1i']], []);
    });

    it("should exec simple ifs scc", function () {
        runTestSet("public function main(b: Bool): Int { if(b) { return 3i; } else { abort; } }", [['true', '3i']], ['false']);
        runTestSet("public function main(b: Bool): Int { if(b) { abort; } else { return 1i; } }", [['false', '1i']], ['true']);

        runTestSet("public function main(b: Bool): Int { if(b) { assert true; } else { return 1i; } return 5i; }", [['false', '1i'], ['true', '5i']], []);
    });

    it("should exec type alias else ifs", function () {
        runTestSet("type Foo = Bool; public function main(b: Foo): Int { if(b || !!b) { return 3i; } else { return 1i; } }", [['true<Main::Foo>', '3i'], ['false<Main::Foo>', '1i']], []);
    });
});
