"use strict";

import { runMainCodeGC } from "../../../bin/test/gc/gc_nf.js"
import { describe, it } from "node:test";

const base = "__CoreCpp::Bool Main::main() {\ngtl_info.disable_automatic_collections = true;";

const first = base.concat("")

//
// Need to fix this fella up to call from our gc_tests.hpp file
//

describe("GC --- tree_basic", () => {
    it("simple tree creation and destruction", function () {
        runMainCodeGC("tree_basic", true);
    });
});