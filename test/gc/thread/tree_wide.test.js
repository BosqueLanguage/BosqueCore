"use strict";

import { runMainCodeGC, thdbase, end } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

const test_1 = thdbase.concat("sharedWideTreeTest_1();", end);
const test_2 = thdbase.concat("sharedWideTreeTest_2();", end);

const multi_test_1 = thdbase.concat("sharedWideTreeTestMulti_1();", end);
const multi_test_2 = thdbase.concat("sharedWideTreeTestMulti_2();", end);

describe("GC --- tree_wide", () => {
    it("shared wide tree creation and destruction", function () {
        runMainCodeGC("tree_wide", "shared_tree_wide", test_1, "true");
        runMainCodeGC("tree_wide", "shared_tree_wide", test_2, "true");
    });

    it("shared multiple wide tree creation and destruction", function () {
        runMainCodeGC("tree_wide", "shared_tree_wide", multi_test_1, "true");
        runMainCodeGC("tree_wide", "shared_tree_wide", multi_test_2, "true");
    });
});
