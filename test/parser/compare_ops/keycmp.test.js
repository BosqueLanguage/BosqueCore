"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- basic KeyComparator equals", () => {
    it("should parse KeyComparator operations", function () {
        parseTestExp("KeyComparator::equal<Nat>(0n, 1n)", undefined, "Bool");
        parseTestExp("KeyComparator::less<Nat>(0n, 1n)", undefined, "Bool");
    });

    it("should parse fail KeyComparator operations", function () {
        parseTestExpError("KeyComparator::equal(0n, 1n)", "KeyComparator expects exactly one (keytype) template argument", "Bool");
        parseTestExpError("KeyComparator::less<Int>(0n 1n)", 'Expected ")" but got "[RECOVER]" when parsing "argument list"', "Bool");
        parseTestExpError("less<Int>(0n, 1n)", "Could not resolve 'less' in this context", "Bool");
    });
});
