"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- Regular Constructor Some", () => {
    it("should emit some/option return", function () {
        checkTestEmitMainFunction("public function main(): Some<Int> { return Some<Int>{3i}; }", 'SomeᐸIntᐳ Mainᕒmain() { return SomeᐸIntᐳ{3_i}; }');
        checkTestEmitMainFunction("public function main(): Option<Int> { return Some<Int>{3i}; }", 'OptionᐸIntᐳ Mainᕒmain() { return OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, SomeᐸIntᐳ{3_i}); }');
    });
});

describe ("CPPEmit -- Regular Constructor Option", () => {
    it("should emit none/option return", function () {
        checkTestEmitMainFunction("public function main(): None { return none; }", 'None Mainᕒmain() { return none; }');
        checkTestEmitMainFunction("public function main(): Option<Int> { return none; }", 'OptionᐸIntᐳ Mainᕒmain() { return OptionᐸIntᐳ::optnone; }');
        checkTestEmitMainFunction("public function main(): Option<Int> { let x = Some<Int>{3i}; return x; }", 'OptionᐸIntᐳ Mainᕒmain() { SomeᐸIntᐳ x = SomeᐸIntᐳ{3_i}; return OptionᐸIntᐳ::fromSome(&ᐸRuntimeᐳ::g_typeinfo_SomeᐸIntᐳ, x); }');
    });
});
