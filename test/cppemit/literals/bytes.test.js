"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Byte", () => {
    it("should emit simple byte", function () {
        checkTestEmitMainFunction("public function main(b: Byte): Byte { return 0xf; }", "Byte Mainᕒmain(Byte b) { return ᐸRuntimeᐳ::XByte{0x0f}; }");
        checkTestEmitMainFunction("public function main(b: Byte): Byte { return 0x0F; }", "Byte Mainᕒmain(Byte b) { return ᐸRuntimeᐳ::XByte{0x0f}; }");
    });
});

describe ("CPPEmit -- ByteBuffer", () => {
    it("should emit simple bytebuffer", function () {
        checkTestEmitMainFunction("public function main(b: ByteBuffer): ByteBuffer { return 0x[]; }", "ByteBuffer Mainᕒmain(ByteBuffer b) { return ᐸRuntimeᐳ::XByteBuffer{}; }");
        checkTestEmitMainFunction("public function main(b: ByteBuffer): ByteBuffer { return 0x[f]; }", "ByteBuffer Mainᕒmain(ByteBuffer b) { return ᐸRuntimeᐳ::XByteBuffer::mk({0x0f}); }");
        checkTestEmitMainFunction("public function main(b: ByteBuffer): ByteBuffer { return 0x[0F]; }", "ByteBuffer Mainᕒmain(ByteBuffer b) { return ᐸRuntimeᐳ::XByteBuffer::mk({0x0f}); }");

        checkTestEmitMainFunction("public function main(b: ByteBuffer): ByteBuffer { return 0x[f,1,10,3f,1f,3,0,0,0]; }", "ByteBuffer Mainᕒmain(ByteBuffer b) { return ᐸRuntimeᐳ::XByteBuffer::mk({0x0f, 0x01, 0x10, 0x3f, 0x1f, 0x03, 0x00, 0x00, 0x00}); }");
    });
});
