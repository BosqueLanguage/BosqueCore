"use strict";

import { runMainCodeGC, thdbase, end } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

const test_2 = thdbase.concat("wideSubtreeTest_2();", end);
const multi_test_2 = thdbase.concat("wideSubtreeTestMulti_2();", end);

describe("GC --- shared_subtree", () => {
    it("wide subtree on second thread survive collection", function () {
        runMainCodeGC("tree_wide", "shared_subtree", test_2, "true");
    });

    it("multiple wide subtree on second thread survive collection", function () {
        runMainCodeGC("tree_wide", "shared_subtree", multi_test_2, "true");
    });
});
