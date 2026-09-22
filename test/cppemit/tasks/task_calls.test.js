"use strict";

import { checkTestEmitMainTask } from "../../../bin/test/cppemit/cppemit_nf.js";
import { describe, it } from "node:test";

describe.skip("CPPEmit Call Function or Method in Tasks", () => {
    it("should handle call function", () => {
        checkTestEmitMainTask("function foo(): Int { return 3i; } public task Main { action start(): APIResult<Int> { return success(foo()); } }", "aaa");
    });

    it("should handle call method", () => {
        checkTestEmitMainTask("public task Main { method m(): Int { return 3i; } action start(): APIResult<Int> { return success(self.m()); } }", "bbb");
    });
});

describe.skip("CPPEmit Call Agent or API in Tasks", () => {
    it("should handle call agent", () => {
        checkTestEmitMainTask("abstract agent foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return agent foo(); } }", "ccc");
        checkTestEmitMainTask("abstract agent foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return agent foo<Int>(); } }", "ddd");
    });

    it("should handle call api", () => {
        checkTestEmitMainTask("abstract api foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return api foo(); } }", "eee");
        checkTestEmitMainTask("abstract api foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return api foo<Int>(); } }", "fff");
    });
});

describe.skip("CPPEmit Call Action in Tasks", () => {
    it("should handle call action", () => {
        checkTestEmitMainTask("public task Main { action foo(): Int { return 3i; } action start(): APIResult<Int> { let v = do self.foo(); return success(v); } }", "ggg");
        checkTestEmitMainTask("public task Main { action foo(): APIResult<Int> { return success(3i); } action start(): APIResult<Int> { return do self.foo(); } }", "hhh");
    });
});


