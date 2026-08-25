"use strict";

import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- Byte", () => {
    it("should exec simple byte", function () {
        runTestSet("public function main(b: Byte): Byte { return 0xf; }", [['0xa', '0xf']], []);
        runTestSet("public function main(b: Byte): Byte { return b; }", [['0xa', '0xa']], []);
    });
});

describe ("CPPExec -- ByteBuffer", () => {
    it("should exec simple bytebuffer", function () {
        runTestSet("public function main(b: ByteBuffer): ByteBuffer { return 0x[]; }", [['0x[]', '0x[]']], []);
        runTestSet("public function main(b: ByteBuffer): ByteBuffer { return 0x[f]; }", [['0x[]', '0x[f]']], []);
        runTestSet("public function main(b: ByteBuffer): ByteBuffer { return 0x[f,1,10,3f,1f,3,0,0,0]; }", [['0x[]', '0x[f,1,10,3f,1f,3,0,0,0]']], []);

        runTestSet("public function main(b: ByteBuffer): ByteBuffer { return b; }", [['0x[]', '0x[]'], ['0x[f]', '0x[f]'], ['0x[f,1,10,3f,1f,3,0,0,0]', '0x[f,1,10,3f,1f,3,0,0,0]']], []);
    });
});
