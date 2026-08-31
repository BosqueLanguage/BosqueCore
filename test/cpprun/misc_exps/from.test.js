"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- from operation", () => {
    it("should exec simple from Number", function () {
        runTestSet("type Foo = Int; public function main(x: Int): Foo { return Foo::from(x); }", [["3i", "3i<Main::Foo>"]], []);

        runTestSet("type Foo = Int & { invariant $value > 0i; } public function main(x: Int): Foo { return Foo::from(x); }", [["3i", "3i<Main::Foo>"]], ["-1i"]); 
    });

    it("should exec simple from CString", function () {
        runTestSet("type Foo = CString; public function main(x: CString): Foo { return Foo::from(x); }", [['"ok"', "'ok'<Main::Foo>"]], []);

        runTestSet("type Foo = CString of /[0-9]{2}/c; public function main(x: CString): Foo { return Foo::from(x); }", [['"12"', "'12'<Main::Foo>"]], ['"0"', '""']); 
    });

    it("should exec simple from String", function () {
        runTestSet('type Foo = String; public function main(x: String): Foo { return Foo::from(x); }', [['"ok"', '"ok"<Main::Foo>']], []);

        runTestSet('type Foo = String of /[0-9]{2}/; public function main(x: String): Foo { return Foo::from(x); }', [['"12"', '"12"<Main::Foo>']], ['"0"', '""']); 
    });
});
