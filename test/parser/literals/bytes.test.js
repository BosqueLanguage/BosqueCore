"use strict";

import { parseTestExp, parseTestExpError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Byte", () => {
    it("should parse simple byte", function () {
        parseTestExp("0xf", undefined, "Byte");
        parseTestExp("0x0F", undefined, "Byte");
    });

    it("should fail invalid bytes", function () {
        parseTestExpError("FF", "Unknown namespace FF", "Byte");
        parseTestExpError("0x1G", 'Expected ";" but got "G" when parsing "line statement"', "Byte");
        parseTestExpError("0x", "Un-annotated numeric literals are not supported", "Byte");
        parseTestExpError("0x100", 'Expected ";" but got "0" when parsing "line statement"', "Byte");
    });
});

describe ("Parser -- ByteBuffer", () => {
    it("should parse simple bytebuffer", function () {
        parseTestExp("0x[]", undefined, "ByteBuffer");
        parseTestExp("0x[f]", undefined, "ByteBuffer");
        parseTestExp("0x[0F]", undefined, "ByteBuffer");

        parseTestExp("0x[f,1,10,3f,1f,3,0,0,0]", undefined, "ByteBuffer");
    });

    it("should fail invalid bytebuffers", function () {
        parseTestExpError("0x[0xf]", "Un-annotated numeric literals are not supported", "ByteBuffer");
        parseTestExpError("0x[GG]", "Un-annotated numeric literals are not supported", "ByteBuffer");

        parseTestExpError("0x[1,3,]", "Un-annotated numeric literals are not supported", "ByteBuffer");
        parseTestExpError("0x[,1]", "Un-annotated numeric literals are not supported", "ByteBuffer");

        parseTestExpError("0x[", 'Un-annotated numeric literals are not supported', "ByteBuffer");
        parseTestExpError("0x]", 'Un-annotated numeric literals are not supported', "ByteBuffer");
    });
});
