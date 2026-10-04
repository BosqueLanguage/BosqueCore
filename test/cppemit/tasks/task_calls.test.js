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
        checkTestEmitMainTask("public task Main { action foo(): Int { return 3i; } action start(): APIResult<Int> { let v = do self.foo(); return success(v); } }", "ggg");
        checkTestEmitMainTask("public task Main { action foo(): APIResult<Int> { return success(3i); } action start(): APIResult<Int> { return do self.foo(); } }", "hhh");
    });
});


