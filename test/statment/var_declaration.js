"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Var Declaration with Let -- basic', function () {
    const testopt = ["statement/var_declaration", "basic_let"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('declare', function () {
        it('expected [1i, [1i, "hello"]]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql('[1i, [1i, "hello"]]');
        });
    });
});

describe('Var Declaration with Var -- basic', function () {
    const testopt = ["statement/var_declaration", "basic_var"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('declare', function () {
        it('expected [2i, [1i, "hello"], 5n]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql('[2i, [1i, "hello"], 5n]');
        });
    });
});

describe('Var Declaration with Var -- flow initialize', function () {
    const testopt = ["statement/var_declaration", "flow_initialize"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('declare(3i)', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, "3i")).to.eql("4i");
        });
    });
});
