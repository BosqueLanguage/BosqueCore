import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- special literals", () => {
    it("should emit true", function () {
        checkTestEmitMainFunction("public function main(): Bool { return true; }", "Bool Mainᕒmain() { return TRUE; }");
    });

    it("should emit false", function () {
        checkTestEmitMainFunction("public function main(): Bool { return false; }", "Bool Mainᕒmain() { return FALSE; }");
    });
});

