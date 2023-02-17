"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Var Declaration with Let -- basic', function () {
    const testopt = ["statement/var_declaration", "basic_let"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('declare', function () {
        it('expected [1, [1, "hello"]]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([1, [["Int", 1], "hello"]]);
        });
    });
});

describe('Var Declaration with Var -- basic', function () {
    const testopt = ["statement/var_declaration", "basic_var"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('declare', function () {
        it('expected [2, [1, "hello"], 5]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([2, [["Int", 1], "hello"], 5]);
        });
    });
});

describe('Var Declaration with Var -- flow initialize', function () {
    const testopt = ["statement/var_declaration", "flow_initialize"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('declare(3)', function () {
        it('expected 2', function () {
            expect(invokeExecutionOn(jsmain, 3)).to.eql(4);
        });
    });
});
