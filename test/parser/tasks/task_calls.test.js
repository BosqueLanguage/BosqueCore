"use strict";

import { parseTaskMainInFile } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe("Call Function or Method", () => {
    it("should handle call function", () => {
        parseTaskMainInFile("function foo(): Int { return 3i; } public task Main { action start(): APIResult<Int> { return success(foo()); } }", "action start(): APIResult<Int> { return success(foo()); }");
    });

    it("should handle call method", () => {
        parseTaskMainInFile("public task Main { method m(): Int { return 3i; } action start(): APIResult<Int> { return success(self.m()); } }", "action start(): APIResult<Int> { return success(self.m()); }");
    });
});

describe("Call Agent or API", () => {
    it("should handle call agent", () => {
        parseTaskMainInFile("abstract agent foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return agent foo(); } }", "action start(): APIResult<Int> { return agent foo(); }");
        parseTaskMainInFile("abstract agent foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return agent foo<Int>(); } }", "action start(): APIResult<Int> { return agent foo<Int>(); }");
    });

    it("should handle call api", () => {
        parseTaskMainInFile("abstract api foo(): APIResult<Int>; public task Main { action start(): APIResult<Int> { return api foo(); } }", "action start(): APIResult<Int> { return api foo(); }");
        parseTaskMainInFile("abstract api foo<T>(): APIResult<T>; public task Main { action start(): APIResult<Int> { return api foo<Int>(); } }", "action start(): APIResult<Int> { return api foo<Int>(); }");
    });
});

describe("Call Action", () => {
    it("should handle call action", () => {
        parseTaskMainInFile("public task Main { action foo(): Int { return 3i; } action start(): APIResult<Int> { let v = action self.foo(); return success(v); } }", "action start(): APIResult<Int> { let v = action self.foo(); return success(v); }");
        parseTaskMainInFile("public task Main { action foo(): APIResult<Int> { return success(3i); } action start(): APIResult<Int> { return action self.foo(); } }", "action start(): APIResult<Int> { return action self.foo(); }");

        parseTaskMainInFile("public task Main { action foo<T>(v: T): APIResult<T> { return success(v); } action start(): APIResult<Int> { return action self.foo<Int>(3i); } }", "action start(): APIResult<Int> { return action foo<Int>(3i); }");
    });
});

