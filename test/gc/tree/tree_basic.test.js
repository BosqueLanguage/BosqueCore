"use strict";

import { runMainCodeGC, treebase, end } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

const test_1 = treebase.concat("basicTreeTest_1();", end);
const test_3 = treebase.concat("basicTreeTest_3();", end);
const test_6 = treebase.concat("basicTreeTest_6();", end);

const multi_test_1 = treebase.concat("basicTreeTestMulti_1();", end);
const multi_test_3 = treebase.concat("basicTreeTestMulti_3();", end);
const multi_test_6 = treebase.concat("basicTreeTestMulti_6();", end);

describe("GC --- tree_basic", () => {
    it("simple tree creation and destruction", function () {
        runMainCodeGC("tree_basic", "tree_basic", test_1, "true");
        runMainCodeGC("tree_basic", "tree_basic", test_3, "true");
        runMainCodeGC("tree_basic", "tree_basic", test_6, "true");
    });

    it("multiple simple tree creation and destruction", function () {
        runMainCodeGC("tree_basic", "tree_basic", multi_test_1, "true");
        runMainCodeGC("tree_basic", "tree_basic", multi_test_3, "true");
        runMainCodeGC("tree_basic", "tree_basic", multi_test_6, "true");
    });
});
