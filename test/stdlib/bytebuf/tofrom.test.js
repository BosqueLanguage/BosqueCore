"use strict";

import { runTestSet } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";


describe ("ByteBuffer -- toFrom Strings", () => {
    it("should to from CString", function () {
        runTestSet("public function main(cstr: CString): ByteBuffer { return CString::toByteBuffer(cstr); }", [['"ok"', "0x[6f,6b]"], ['""', "0x[]"], ['" "', "0x[20]"]], []);
        runTestSet("public function main(bb: ByteBuffer): Option<CString> { return CString::fromByteBuffer(bb); }", [["0x[6f,6b]", "some('ok')"], ["0x[]", "some('')"], ["0x[20]", "some(' ')"], ["0x[20,0]", "none"]], []);
    });
});