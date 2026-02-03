"use strict";

import { runMainCodeGC, treebase, end } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

const test_1 = treebase.concat("wideTreeTest_1();", end);
const test_2 = treebase.concat("wideTreeTest_2();", end);

const multi_test_1 = treebase.concat("wideTreeTestMulti_1();", end);
const multi_test_2 = treebase.concat("wideTreeTestMulti_2();", end);

describe("GC --- tree_wide", () => {
    it("wide tree creation and destruction", function () {
        runMainCodeGC("tree_wide", "tree_wide", test_1, "true");
        runMainCodeGC("tree_wide", "tree_wide", test_2, "true");
    });

    it("multiple wide tree creation and destruction", function () {
        runMainCodeGC("tree_wide", "tree_wide", multi_test_1, "true");
        runMainCodeGC("tree_wide", "tree_wide", multi_test_2, "true");
    });
});
