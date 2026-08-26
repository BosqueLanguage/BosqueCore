"use strict";

import { checkTestExp } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe ("Checker -- Byte", () => {
    it("should check simple byte", function () {
        checkTestExp("0xf", "Byte");
        checkTestExp("0x0F", "Byte");
    });
});

describe ("Checker -- ByteBuffer", () => {
    it("should check simple bytebuffer", function () {
        checkTestExp("0x[]", "ByteBuffer");
        checkTestExp("0x[f]", "ByteBuffer");
        checkTestExp("0x[0F]", "ByteBuffer");

        checkTestExp("0x[f,1,10,3f,1f,3,0,0,0]", "ByteBuffer");
    });
});

