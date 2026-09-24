"use strict";

import { checkTestEmitMainTask } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe.skip("CPPEmit Task Declarations", () => {
    it("should emit a valid Main task", () => {
        checkTestEmitMainTask("public task Main { action start(): APIResult<Int> { return success(3i); } }", "xxxx");
    });
});

