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
            expect(invokeExecutionOn(jsmain, "none")).to.includes("cannot convert value");
        });
    });
    describe('process(2n)', function () {
        it('expected 12n', function () {
            expect(invokeExecutionOn(jsmain, "2n")).to.eql("12n");
        });
    });
});

describe('Var Retype flow', function () {
    const testopt = ["statement/var_retype", "flow"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(none)', function () {
        it('expected 0n', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0n");
        });
    });
    describe('process(2n)', function () {
        it('expected 12n', function () {
            expect(invokeExecutionOn(jsmain, "2n")).to.eql("12n");
        });
    });
});


describe('Var Retype join', function () {
    const testopt = ["statement/var_retype", "join"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(none)', function () {
        it('expected 10n', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("10n");
        });
    });
    describe('process(2n)', function () {
        it('expected 12n', function () {
            expect(invokeExecutionOn(jsmain, "2n")).to.eql("12n");
        });
    });
});
