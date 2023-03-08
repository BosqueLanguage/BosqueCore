"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Var Retype simple', function () {
    const testopt = ["statement/var_retype", "simple"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(none)', function () {
        it('expected ', function () {
            expect(invokeExecutionOn(jsmain, null)).to.includes("error -- cannot convert value");
        });
    });
    describe('process(2)', function () {
        it('expected 12', function () {
            expect(invokeExecutionOn(jsmain, 2)).to.eql(12);
        });
    });
});

describe('Var Retype flow', function () {
    const testopt = ["statement/var_retype", "flow"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(none)', function () {
        it('expected ', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql(0);
        });
    });
    describe('process(2)', function () {
        it('expected 12', function () {
            expect(invokeExecutionOn(jsmain, 2)).to.eql(12);
        });
    });
});


describe('Var Retype join', function () {
    const testopt = ["statement/var_retype", "join"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(none)', function () {
        it('expected ', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql(10);
        });
    });
    describe('process(2)', function () {
        it('expected 12', function () {
            expect(invokeExecutionOn(jsmain, 2)).to.eql(12);
        });
    });
});
