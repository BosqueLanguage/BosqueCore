"use strict";

import { runMainCodeGC } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

const base = "__CoreCpp::Bool main() {gtl_info.disable_automatic_collections = true;";
const end = "verifyTest();return true;}"

const test_1 = base.concat("basicTreeTest_1();", end);
const test_3 = base.concat("basicTreeTest_3();", end);
const test_6 = base.concat("basicTreeTest_6();", end);

describe("GC --- tree_basic", () => {
    it("simple tree creation and destruction", function () {
        runMainCodeGC("tree_basic", test_1, "true");
        runMainCodeGC("tree_basic", test_3, "true");
        runMainCodeGC("tree_basic", test_6, "true");
    });
});