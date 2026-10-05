"use strict";

import { checkTestEmitMainTask } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe("CPPEmit Call Function or Method in Tasks", () => {
    it("should handle call function", () => {
        checkTestEmitMainTask("function foo(): Int { return 3i; } public task Main { action start(): APIResult<Int> { return success(foo()); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { Int tmp_0 = Mainᕒfoo(); return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, tmp_0}}; }');
    });

    it("should handle call method", () => {
        checkTestEmitMainTask("public task Main { method m(): Int { return 3i; } action start(): APIResult<Int> { return success(self.m()); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { Int tmp_0 = MainᕒMainᑀm(self); return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, tmp_0}}; }');
    });
});

describe("CPPEmit Call Agent or API in Tasks", () => {
    it("should handle call agent", () => {
        checkTestEmitMainTask("abstract agent foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return agent foo(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ tmp_0 = Main::foo(); return tmp_0; }');
        checkTestEmitMainTask("abstract agent foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return agent foo<Int>(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ tmp_0 = Main::foo(2); return tmp_0; }');
    });

    it("should handle call api", () => {
        checkTestEmitMainTask("abstract api foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return api foo(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ tmp_0 = Main::foo(); return tmp_0; }');
        checkTestEmitMainTask("abstract api foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return api foo<Int>(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ tmp_0 = Main::foo(2); return tmp_0; }');
    });
});

describe("CPPEmit Call Action in Tasks", () => {
    it("should handle call action", () => {
        checkTestEmitMainTask("public task Main { action foo(): Int { return 3i; } action start(): APIResult<Int> { let v = do self.foo(); return success(v); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { Int tmp_0 = MainᕒMainᑀfoo(self); Int v = tmp_0; return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, v}}; }');
        checkTestEmitMainTask("public task Main { action foo(): APIResult<Int> { return success(3i); } action start(): APIResult<Int> { return do self.foo(); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self) { APIResultᐸIntᐳ tmp_0 = MainᕒMainᑀfoo(self); return tmp_0; }');
    });

    it("should handle call action with pre/post", () => {
        checkTestEmitMainTask("public task Main { action foo(x: Int): Int requires x > 0i; { return x + 1i; } action start(k: Int): APIResult<Int> { let v = do self.foo(k); return success(v); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self, Int k) { ᐸRuntimeᐳ::bsq_requires((bool)(MainᕒMainᑀfooᐤrequires_0(self, k)), "test.bsq", 2, nullptr, "Failed Requires"); Int tmp_0 = MainᕒMainᑀfoo(self, k); Int v = tmp_0; return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, v}}; }');
        checkTestEmitMainTask("public task Main { action foo(x: Int): Int requires x > 0i; ensures $return > 0i; { return x + 1i; } action start(k: Int): APIResult<Int> { let v = do self.foo(k); return success(v); } }", 'APIResultᐸIntᐳ MainᕒMainᑀstart(MainᕒMain& self, Int k) { ᐸRuntimeᐳ::bsq_requires((bool)(MainᕒMainᑀfooᐤrequires_0(self, k)), "test.bsq", 2, nullptr, "Failed Requires"); MainᕒMain tmp_1 = self; Int tmp_0 = MainᕒMainᑀfoo(self, k); ᐸRuntimeᐳ::bsq_ensures((bool)(MainᕒMainᑀfooᐤensures_0(tmp_0, tmp_1, self, k)), "test.bsq", 2, nullptr, "Failed Ensures"); Int v = tmp_0; return APIResultᐸIntᐳ{APIResultᐸIntᐳᕒSuccess{{}, v}}; }');
    });
});


