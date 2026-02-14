"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- access enum", () => {
    it("should emit simple enum access", function () {
        checkTestEmitMainFunction("enum Foo {f, g} public function main(): Foo { return Foo#f; }", "MainᕒFoo Mainᕒmain() { return MainᕒFoo::f; }");
        checkTestEmitMainFunction("enum Foo {f, g} public function main(): Foo { return Foo#g; }", "MainᕒFoo Mainᕒmain() { return MainᕒFoo::g; }");
    });
});
