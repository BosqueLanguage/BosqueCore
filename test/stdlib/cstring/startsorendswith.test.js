"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe("CString startsOrEndsWith tests", () => {
    it("should test startsWith", () => {
        runTestSet("public function main(s: CString): Bool { return s.startsWith<CString>(''); }", [['"abc"', "true"], ['""', "true"]], []);
        runTestSet("public function main(s: CString): Bool { return s.startsWith<CRegex>(/[0-9]*/c); }", [['"abc"', "true"], ['""', "true"]], []);

        runTestSet("public function main(s: CString): Bool { return s.startsWith<CString>('123'); }", [['"abc"', "false"], ['"123abc"', "true"], ['"abc123"', "false"], ['"123"', "true"], ['"1"', "false"], ['""', "false"]], []);
        runTestSet("public function main(s: CString): Bool { return s.startsWith<CChar>(c'1'); }", [['"abc"', "false"], ['"123abc"', "true"], ['"abc123"', "false"], ['"123"', "true"], ['"1"', "true"], ['""', "false"]], []);
        runTestSet("public function main(s: CString): Bool { return s.startsWith<CRegex>(/[0-9]+/c); }", [['"abc"', "false"], ['"123abc"', "true"], ['"abc123"', "false"], ['"123"', "true"], ['"1"', "true"], ['""', "false"]], []);
    });

    it("should test endsWith", () => {
        runTestSet("public function main(s: CString): Bool { return s.endsWith<CString>(''); }", [['"abc"', "true"], ['""', "true"]], []);

        runTestSet("public function main(s: CString): Bool { return s.endsWith<CString>('123'); }", [['"abc"', "false"], ['"123abc"', "false"], ['"abc123"', "true"], ['"123"', "true"], ['"1"', "false"], ['""', "false"]], []);
        runTestSet("public function main(s: CString): Bool { return s.endsWith<CChar>(c'3'); }", [['"abc"', "false"], ['"123abc"', "false"], ['"abc123"', "true"], ['"123"', "true"], ['"1"', "false"], ['"3"', "true"], ['""', "false"]], []);
        
        //TODO: we don't support regex for endsWith yet
        // runTestSet("public function main(s: CString): Bool { return s.endsWith<CRegex>(/[0-9]+/c); }", [['"abc"', "false"], ['"123abc"', "false"], ['"abc123"', "true"], ['"123"', "true"], ['"1"', "true"], ['""', "false"]], []);
    });
});
