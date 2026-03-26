"use strict";

import { parseTestFunction, parseTestFunctionError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Postfix @", () => {
    it("should parse postfix @ option", function () {
        parseTestFunction("function main(x: Option<Int>): None { return x@none; }", undefined);
        parseTestFunction("function main(x: Option<Int>): Some<Int> { return x@!none; }", undefined);

        parseTestFunction("function main(x: Option<Int>): Some<Int> { return x@some; }", undefined);
        parseTestFunction("function main(x: Option<Int>): None { return x@!some; }", undefined);
    });

    it("should parse postfix @ option fails", function () {
        parseTestFunctionError("function main(x: Option<Int>): Bool { return x!@none; }", "ITest guard expression is missing parentheses");
        parseTestFunctionError("function main(x: Option<Int>): Bool { return x@!!none; }", "Expected ITest");
    });

    it("should parse postfix @ types", function () {
        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Foo { return x@<Foo>; }", "function main(x: Bar): Foo { return x@<Foo>; }");
        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bar { return x@!<Foo>; }", "function main(x: Bar): Bar { return x@!<Foo>; }");

        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bar { return x@<Bar>; }", "function main(x: Bar): Bar { return x@<Bar>; }");
        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Bar { return x@<Bar>; }", "function main(x: Foo): Bar { return x@<Bar>; }");
        parseTestFunction("concept Baz {} concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Baz { return x@<Baz>; }", "function main(x: Foo): Baz { return x@<Baz>; }");
    });

    it("should parse postfix @ types fails", function () {
        parseTestFunctionError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x@Foo>; }", "Expected ITest");
        parseTestFunctionError("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bool { return x@!<Foo; }", 'Expected ">" but got ";" when parsing "ITest"');
    });
});

