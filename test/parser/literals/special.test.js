"use strict";

import { parseTestExp } from "/home/mark/Code/BosqueCore/bin/test/parser/parse_nf.js";

import { describe, it } from "node:test";
import assert from "node:assert";

describe ("Parser -- special literals", () => {
    it("should parse none", () => {
        parseTestExp("none", "None");
    });
    
    it("should parse nothing", function () {
        parseTestExp("nothing", "Nothing");
    });

    it("should parse true", function () {
        parseTestExp("true", "Bool");
    });

    it("should parse false", function () {
        parseTestExp("false", "Bool");
    });
});

describe ("Parser -- Int", () => {
    it("should parse simple integers", function () {
        parseTestExp("0i", "Int");
    });
});