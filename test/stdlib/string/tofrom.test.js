"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("String -- convert to/from CString", () => {
    it("should convert from CString", function () {
        runTestSet('public function main(z: CString): String { return String::fromCString(z); }', [['""', '""'], ['"non-empty"', '"non-empty"']], []);
    });

    it("should convert to CString", function () {
        runTestSet('public function main(z: String): Option<CString> { return String::toCString(z); }', [['""', "some('')"], ['"non-empty"', "some('non-empty')"], ['"x🌵z"', "none"]], []);
    });
});

