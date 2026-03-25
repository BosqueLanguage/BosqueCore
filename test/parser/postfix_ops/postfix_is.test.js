"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Postfix ?", () => {
    it("should parse postfix ? option", function () {
        parseTestFunction("function main(x: Option<Int>): Bool { return x?none; }", undefined);
        parseTestFunction("function main(x: Option<Int>): Bool { return x?!none; }", undefined);

        parseTestFunction("function main(x: Option<Int>): Bool { return x?some; }", undefined);
        parseTestFunction("function main(x: Option<Int>): Bool { return x?!some; }", undefined);
    });

    it("should parse postfix ? option fails", function () {
        parseTestFunctionError("function main(x: Option<Int>): Bool { return x??none; }", "Expected ITest");
        parseTestFunctionError("function main(x: Option<Int>): Bool { return x?!!none; }", "Expected ITest");
    });

    it("should parse postfix ? types", function () {
        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x?<Foo>; }", "function main(x: Bar): Bool { return x?<Foo>; }");
        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x?!<Foo>; }", "function main(x: Bar): Bool { return x?!<Foo>; }");
    });

    it("should parse postfix ? types fails", function () {
        parseTestFunctionError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x?Foo>; }", "Expected ITest");
        parseTestFunctionError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x?!<Foo; }", 'Expected ">" but got ";" when parsing "ITest"');
    });
});

