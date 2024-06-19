import { parseTestExp, parseTestExpError, parseTestFunction } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- if-expression", () => {
    it("should parse expressions", function () {
        parseTestExp("if(true) then 2i else 3i + 5i", undefined, "Int");
        parseTestExp("if(3n != 2n) then 2i else (3i + 5i)", "if(3n != 2n) then 2i else 3i + 5i", "Int");
        parseTestExp("(if(false) then 2i else 3i) + 5i", undefined, "Int");
    });

    it("should parse expressions w/ itest", function () {
        parseTestExp("if(true)!none then 2i else 3i", undefined, "Int");
        parseTestExp("if(3n)some then 2i else 3i", undefined, "Int");
        parseTestExp("if(3n)<Some> then 2i else 3i", undefined, "Int");
        parseTestExp("if(if(true) then false else true) then 2i else 3i", undefined, "Int");

        parseTestFunction("function main(x: Int?): Int { return if(x)@!none then $x else 3i; }", undefined);
        parseTestFunction("function main(x: Int?): Int { return if(x + 1i)@!none then $_ else 3i; }", undefined);
        parseTestFunction("function main(x: Int?): Int { return if($y = x + 1i)@<Some> then $y else 3i; }", undefined);
    });

    it("should fail missing then", function () {
        parseTestExpError("if(true) 3n else 5n", 'Expected ITest', "Nat");
    });

    it("should fail missing )", function () {
        parseTestExpError("if(3n != 2n then true else false", 'Expected ")" but got "then" when parsing "if test"', "Bool");
    });

    it("should fail missing else", function () {
        parseTestExpError("if(3n != 2n) then true || false false", 'Expected "else" but got "false" when parsing "if-expression"', "Bool");
    });

    it("should fail bad-binder", function () {
        parseTestExpError("if(3n)@@!none then true else false", 'Cannot have postflow in if-expression', "Bool");
    });

    it("should fail bad-binder name", function () {
        parseTestExpError("if(y = 3n)@@!none then true else false", 'Invalid binder name -- must start with $ followed by a valid identifier name', "Bool");
    });
});


