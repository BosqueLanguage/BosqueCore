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

    it("should parse postfix @ types", function () {
        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Foo { return x@<Foo>; }", undefined);
        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bar { return x@!<Foo>; }", undefined);

        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Bar): Bar { return x@<Bar>; }", undefined);
        parseTestFunction("concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Bar { return x@<Bar>; }", undefined);
        parseTestFunction("concept Baz {} concept Bar {} entity Foo provides Bar { field f: Int; } function main(x: Foo): Baz { return x@<Baz>; }", undefined);
    });
});

