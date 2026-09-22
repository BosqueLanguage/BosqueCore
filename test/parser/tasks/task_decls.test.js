"use strict";

import { parseTaskMainInFile, parseTestTaskMainInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe("Parser Task Declarations", () => {
    it("should parse a valid Main task", () => {
        parseTaskMainInFile("public task Main { action start(): APIResult<Int> { return success(3i); } }", "action start(): APIResult<Int> { return success(3i); }");
    });

    it("should fail task", () => {
        parseTestTaskMainInFileError("public task Main { action start() { return success(3i); } }", "Failed to find namespace declaration");
    });
});

