"use strict";

import { checkTestTaskInFile, checkTestTaskInFileError } from "../../../bin/test/typecheck/typecheck_nf.js";
import { describe, it } from "node:test";

describe("Typecheck Call Function or Method in Tasks", () => {
    it("should handle call function", () => {
        checkTestTaskInFile("function foo(): Int { return 3i; } public task Main { action start(): APIResult<Int> { return success(foo()); } }");
    });

    it("should handle call method", () => {
        checkTestTaskInFile("public task Main { method m(): Int { return 3i; } action start(): APIResult<Int> { return success(self.m()); } }");
    });
});

describe("Typecheck Call Agent or API in Tasks", () => {
    it("should handle call agent", () => {
        checkTestTaskInFile("abstract agent foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return agent foo(); } }");
        checkTestTaskInFile("abstract agent foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return agent foo<Int>(); } }");
    });

    it("should handle call api", () => {
        checkTestTaskInFile("abstract api foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return api foo(); } }");
        checkTestTaskInFile("abstract api foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return api foo<Int>(); } }");
    });
});

describe("Typecheck Call Action in Tasks", () => {
    it("should handle call action", () => {
        checkTestTaskInFile("public task Main { action foo(): Int { return 3i; } action start(): APIResult<Int> { let v = do self.foo(); return success(v); } }");
        checkTestTaskInFile("public task Main { action foo(): APIResult<Int> { return success(3i); } action start(): APIResult<Int> { return do self.foo(); } }");
    });
});

