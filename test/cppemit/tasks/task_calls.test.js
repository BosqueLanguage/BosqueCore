"use strict";

import { checkTestEmitMainTask } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe("CPPEmit Call Function or Method in Tasks", () => {
    it("should handle call function", () => {
        checkTestEmitMainTask("function foo(): Int { return 3i; } public task Main { action start(): APIResult<Int> { return success(foo()); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { Int ᐸtmp_0ᐳ = Mainᕒfoo(); return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, ᐸtmp_0ᐳ}}; }');
    });

    it("should handle call method", () => {
        checkTestEmitMainTask("public task Main { method m(): Int { return 3i; } action start(): APIResult<Int> { return success(self.m()); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { Int ᐸtmp_0ᐳ = MainᕒMainᑀm(self); return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, ᐸtmp_0ᐳ}}; }');
    });
});

describe("CPPEmit Call Agent or API in Tasks", () => {
    it("should handle call agent", () => {
        checkTestEmitMainTask("abstract agent foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return agent foo(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ ᐸtmp_0ᐳ = Main::foo(); return ᐸtmp_0ᐳ; }');
        checkTestEmitMainTask("abstract agent foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return agent foo<Int>(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ ᐸtmp_0ᐳ = Main::foo(2); return ᐸtmp_0ᐳ; }');
    });

    it("should handle call api", () => {
        checkTestEmitMainTask("abstract api foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return api foo(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ ᐸtmp_0ᐳ = Main::foo(); return ᐸtmp_0ᐳ; }');
        checkTestEmitMainTask("abstract api foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return api foo<Int>(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ ᐸtmp_0ᐳ = Main::foo(2); return ᐸtmp_0ᐳ; }');
    });
});

describe("CPPEmit Call Action in Tasks", () => {
    it("should handle call action", () => {
        checkTestEmitMainTask("public task Main { action foo(): Int { return 3i; } action start(): APIResult<Int> { let v = do self.foo(); return success(v); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { Int ᐸtmp_0ᐳ = MainᕒMainᑀfoo(self); Int v = ᐸtmp_0ᐳ; return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, v}}; }');
        checkTestEmitMainTask("public task Main { action foo(): APIResult<Int> { return success(3i); } action start(): APIResult<Int> { return do self.foo(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ ᐸtmp_0ᐳ = MainᕒMainᑀfoo(self); return ᐸtmp_0ᐳ; }');
    });

    it("should handle call action with pre/post", () => {
        checkTestEmitMainTask("public task Main { action foo(x: Int): Int requires x > 0i; { return x + 1i; } action start(k: Int): APIResult<Int> { let v = do self.foo(k); return success(v); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self, Int k) { ᐸRuntimeᐳ::bsq_requires((bool)(MainᕒMainᑀfooᐤrequires_0(self, k)), "test.bsq", 2, nullptr, "Failed Requires"); Int ᐸtmp_0ᐳ = MainᕒMainᑀfoo(self, k); Int v = ᐸtmp_0ᐳ; return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, v}}; }');
        checkTestEmitMainTask("public task Main { action foo(x: Int): Int requires x > 0i; ensures $return > 0i; { return x + 1i; } action start(k: Int): APIResult<Int> { let v = do self.foo(k); return success(v); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self, Int k) { ᐸRuntimeᐳ::bsq_requires((bool)(MainᕒMainᑀfooᐤrequires_0(self, k)), "test.bsq", 2, nullptr, "Failed Requires"); MainᕒMain ᐸtmp_1ᐳ = self; Int ᐸtmp_0ᐳ = MainᕒMainᑀfoo(self, k); ᐸRuntimeᐳ::bsq_ensures((bool)(MainᕒMainᑀfooᐤensures_0(ᐸtmp_0ᐳ, ᐸtmp_1ᐳ, self, k)), "test.bsq", 2, nullptr, "Failed Ensures"); Int v = ᐸtmp_0ᐳ; return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, v}}; }');
    });
});


