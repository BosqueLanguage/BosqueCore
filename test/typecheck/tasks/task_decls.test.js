"use strict";

import { checkTestTaskInFile, checkTestTaskInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe("Typecheck Task Declarations", () => {
    it("should check a valid Main task", () => {
        checkTestTaskInFile("public task Main { action start(): APIResult<Int> { return success(3i); } }");
    });

    it("should fail task", () => {
        checkTestTaskInFileError("public task Main { }", "Missing start action on Task");

        checkTestTaskInFileError("public task Main { action start(): Int { return 3i; } }", "Result of start action must be either a single result OR a result and event message");
        checkTestTaskInFileError("public task Main { action start(): APIResult<Int> { return 3i; } }", "Expected a return value of type APIResult<Int> but got Int");
    });
});

