"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe("String startsOrEndsWith tests", () => {
    it("should test startsWith", () => {
        runTestSet('public function main(s: String): Bool { return s.startsWith<String>(""); }', [['"abc"', "true"], ['""', "true"]], []);
        runTestSet('public function main(s: String): Bool { return s.startsWith<Regex>(/[0-9]*/); }', [['"abc"', "true"], ['""', "true"]], []);

        runTestSet('public function main(s: String): Bool { return s.startsWith<String>("123"); }', [['"abc"', "false"], ['"123abc"', "true"], ['"abc123"', "false"], ['"123"', "true"], ['"1"', "false"], ['""', "false"]], []);
        runTestSet('public function main(s: String): Bool { return s.startsWith<UnicodeChar>(c"1"); }', [['"abc"', "false"], ['"123abc"', "true"], ['"abc123"', "false"], ['"123"', "true"], ['"1"', "true"], ['""', "false"]], []);
        runTestSet('public function main(s: String): Bool { return s.startsWith<Regex>(/[0-9]+/); }', [['"abc"', "false"], ['"123abc"', "true"], ['"abc123"', "false"], ['"123"', "true"], ['"1"', "true"], ['""', "false"]], []);
    });

    it("should test endsWith", () => {
        runTestSet('public function main(s: String): Bool { return s.endsWith<String>(""); }', [['"abc"', "true"], ['""', "true"]], []);

        runTestSet('public function main(s: String): Bool { return s.endsWith<String>("123"); }', [['"abc"', "false"], ['"123abc"', "false"], ['"abc123"', "true"], ['"123"', "true"], ['"1"', "false"], ['""', "false"]], []);
        runTestSet('public function main(s: String): Bool { return s.endsWith<UnicodeChar>(c"3"); }', [['"abc"', "false"], ['"123abc"', "false"], ['"abc123"', "true"], ['"123"', "true"], ['"1"', "false"], ['"3"', "true"], ['""', "false"]], []);
        
        //TODO: we don't support regex for endsWith yet
        // runTestSet("public function main(s: String): Bool { return s.endsWith<CRegex>(/[0-9]+/c); }", [['"abc"', "false"], ['"123abc"', "false"], ['"abc123"', "true"], ['"123"', "true"], ['"1"', "true"], ['""', "false"]], []);
    });
});
