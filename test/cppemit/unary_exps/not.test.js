"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Simple Boolean not", () => {
    it("should emit (simplify) simple not", function () {
        checkTestEmitMainFunction("public function main(): Bool { return !false; }", "Bool Mainᕒmain() { return TRUE; }");
        checkTestEmitMainFunction("public function main(): Bool { return !!true; }", "Bool Mainᕒmain() { return TRUE; }");
    });

    it("should emit simple not", function () {
        checkTestEmitMainFunction("public function main(x: Bool): Bool { return !x; }", "Bool Mainᕒmain(Bool x) { return !x; }");
        checkTestEmitMainFunction("public function main(x: Bool): Bool { return !!x; }", "Bool Mainᕒmain(Bool x) { return x; }");
    });

    it("should emit type alias not", function () {
        checkTestEmitMainFunction("type Foo = Bool; public function main(x: Foo): Foo { return !x; }", "MainᕒFoo Mainᕒmain(MainᕒFoo x) { return MainᕒFoo{!(x.value)}; }");
        checkTestEmitMainFunction("type Foo = Bool; public function main(x: Foo): Foo { return !!x; }", "MainᕒFoo Mainᕒmain(MainᕒFoo x) { return MainᕒFoo{!((MainᕒFoo{(!(x.value))}).value)}; }");
    });
});
