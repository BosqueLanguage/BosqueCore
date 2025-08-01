"use strict";

import { runMainCodeGC } from "../gc_nf.ts"
import { describe, it } from "node:test";

describe("GC --- tree_basic", () => {
    it("simple tree creation and destruction", function () {
        runMainCodeGC("tree_basic", true);
    });
});