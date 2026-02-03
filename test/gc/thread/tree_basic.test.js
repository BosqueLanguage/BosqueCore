"use strict";

import { runMainCodeGC, thdbase, end } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

const test_1 = thdbase.concat("sharedBasicTreeTest_1();", end);
const test_3 = thdbase.concat("sharedBasicTreeTest_3();", end);
const test_6 = thdbase.concat("sharedBasicTreeTest_6();", end);

const multi_test_1 = thdbase.concat("sharedBasicTreeTestMulti_1();", end);
const multi_test_3 = thdbase.concat("sharedBasicTreeTestMulti_3();", end);
const multi_test_6 = thdbase.concat("sharedBasicTreeTestMulti_6();", end);

describe("GC --- shared_tree_basic", () => {
    it("simple shared tree creation and destruction", function () {
        runMainCodeGC("tree_basic", "shared_tree_basic", test_1, "true");
        //runMainCodeGC(tree_basic", "shared_tree_basic", test_3, "true");
        //runMainCodeGC(tree_basic", "shared_tree_basic", test_6, "true");
    });

/*
    it("multiple simple tree creation and destruction", function () {
        runMainCodeGC(tree_basic", "shared_tree_basic", multi_test_1, "true");
        runMainCodeGC(tree_basic", "shared_tree_basic", multi_test_3, "true");
        runMainCodeGC(tree_basic", "shared_tree_basic", multi_test_6, "true");
    });
*/
});
