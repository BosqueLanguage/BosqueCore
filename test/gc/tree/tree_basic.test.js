"use strict";

import { runMainCodeGC } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

// set up global array, disable stack refs
const base = "__CoreCpp::Bool main() { GlobalDataStorage::g_global_data.initialize(sizeof(garray), (void**)garray); gtl_info.disable_stack_refs_for_tests = true; gtl_info.enable_global_rescan = true;\n";
const end = "\nreturn true;}"

const test_1 = base.concat("basicTreeTest_1();", end);
const test_3 = base.concat("basicTreeTest_3();", end);
const test_6 = base.concat("basicTreeTest_6();", end);

const multi_test_1 = base.concat("basicTreeTestMulti_1();", end);
const multi_test_3 = base.concat("basicTreeTestMulti_3();", end);
const multi_test_6 = base.concat("basicTreeTestMulti_6();", end);

describe("GC --- tree_basic", () => {
    it("simple tree creation and destruction", function () {
        runMainCodeGC("tree_basic", test_1, "true");
        runMainCodeGC("tree_basic", test_3, "true");
        runMainCodeGC("tree_basic", test_6, "true");
    });

    it("multiple simple tree creation and destruction", function () {
        runMainCodeGC("tree_basic", multi_test_1, "true");
        runMainCodeGC("tree_basic", multi_test_3, "true");
        runMainCodeGC("tree_basic", multi_test_6, "true");
    });
});