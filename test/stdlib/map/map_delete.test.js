"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Map -- delete", () => {
    it("should delete existing keys", function () {
        runMainCode('public function main(): Bool { return Map<Int, Bool>{ 1i => true, 2i => false }.s_map_delete(2i).size() === 1n', "true"); 

    });
});
