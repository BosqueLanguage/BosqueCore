import { runMainCode, runMainCodeError } from "../../../bin/test/stdlib/stdlib_nf.js";
import { describe, it } from "node:test";

describe ("Float -- builtins", () => {
    it("consts", function () {
        runMainCode('public function main(): Float { return Float::pi; }', "3.141592653589793f"); 
        runMainCode('public function main(): Float { return Float::e; }', "2.718281828459045f"); 
    });

    it("min/max", function () {
        runMainCode('public function main(): Float { return Float::min(3.0f, 1.0f); }', "1.0f"); 
        runMainCode('public function main(): Float { return Float::max(3.0f, 1.0f); }', "3.0f");

        runMainCode('public function main(): Bool { return Float::min(0.0f, 0.0f) == 0.0f && Float::max(0.0f, 0.0f) == 0.0f; }', "true");
        runMainCode('public function main(): Bool { return Float::min(0.0f, 1.0f) == Float::max(-10.0f, 0.0f); }', "true");
    });

    it("square/cube", function () {
        runMainCode('public function main(): Float { return Float::square(3.0f); }', "9.0f"); 
        runMainCode('public function main(): Float { return Float::cube(3.0f); }', "27.0f"); 
    });

    it("sqrt", function () {
        runMainCode('public function main(): Float { return Float::sqrt(9.0f); }', "3.0f");

        runMainCode('public function main(): Float { return Float::sqrt(1.0f); }', "1.0f"); 
        runMainCode('public function main(): Float { return Float::sqrt(0.0f); }', "0.0f"); 

        runMainCodeError('public function main(): Float { return Float::sqrt(-9.0f); }', "Error -- x >= 0.0f @ core.bsq"); 
    });
});
