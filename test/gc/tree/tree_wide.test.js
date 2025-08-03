"use strict";

import { runMainCodeGC } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

const base = "__CoreCpp::Bool main() {gtl_info.disable_automatic_collections = true;";
const end = "verifyTest();return true;}"

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