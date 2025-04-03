"use strict";

import { runMainCode } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Map -- delete", () => {
    it("should delete existing keys", function () {
        runMainCode('public function main(): Nat { return Map<Int, Int>{1i => 0i, 3i => 5i}.delete(1i).size(); }', "1n"); 

        // A better way to test would be to run has on the key we removed
    });
});
