"use strict";

import { checkTestEmitMainFunction } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe ("CPPEmit -- simple debug", () => {
    it("should emit simple debug", function () {
        checkTestEmitMainFunction("public function main(): Int { if(true) { _debug 5i; } return 1i; }", 'Int Mainᕒmain() { { auto __val = 5_i; std::cout << "**DIAGNOSTIC**" << std::endl; ᐸRuntimeᐳ::g_typeinfo_Int.opdispatch.displayFp(&ᐸRuntimeᐳ::g_typeinfo_Int, &__val, std::cout, std::nullopt); std::cout << std::endl; } return 1_i; }');
        checkTestEmitMainFunction("entity Foo { field f: Int; }public function main(x: Foo): Int {  _debug x; return 1i; }", 'Int Mainᕒmain(MainᕒFoo x) { { auto __val = x; std::cout << "**DIAGNOSTIC**" << std::endl; ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo.opdispatch.displayFp(&ᐸRuntimeᐳ::g_typeinfo_MainᕒFoo, &__val, std::cout, std::nullopt); std::cout << std::endl; } return 1_i; }');
    });
});
