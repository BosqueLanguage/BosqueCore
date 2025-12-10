"use strict";

import { runMainCodeGC } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

// set up global array, disable stack refs
const base = "__CoreCpp::Bool main() { GlobalDataStorage::g_global_data.initialize(sizeof(garray), (void**)garray); gtl_info.disable_stack_refs_for_tests = true; gtl_info.enable_global_rescan = true;\n";
const end = "\nreturn true;}"

const test_1 = base.concat("wideTreeTest_1();", end);
const test_2 = base.concat("wideTreeTest_2();", end);

const multi_test_1 = base.concat("wideTreeTestMulti_1();", end);
const multi_test_2 = base.concat("wideTreeTestMulti_2();", end);

describe("GC --- tree_wide", () => {
    it("wide tree creation and destruction", function () {
        runMainCodeGC("tree_wide", test_1, "true");
        runMainCodeGC("tree_wide", test_2, "true");
    });

    it("multiple wide tree creation and destruction", function () {
        runMainCodeGC("tree_wide", multi_test_1, "true");
        runMainCodeGC("tree_wide", multi_test_2, "true");
    });
});