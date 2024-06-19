"use strict";

import { parseTestExp } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- special literals", () => {
    it("should parse none", () => {
        parseTestExp("none", undefined, "None");
    });
    
    it("should parse nothing", function () {
        parseTestExp("nothing", undefined, "Nothing");
    });

    it("should parse true", function () {
        parseTestExp("true", undefined, "Bool");
    });

    it("should parse false", function () {
        parseTestExp("false", undefined, "Bool");
    });
});
