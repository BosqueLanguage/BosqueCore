"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Addition', function () {
    const testopt = ["expression/bin_arith_ops", "addop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('addop 1, 3.0, 3/2, 10', function () {
        it('expected [2, 0.0, "11/6", 11]', function () {
            expect(invokeExecutionOn(jsmain, "1i", "3.0f", "3/2R", "10N_Foo")).to.eql([2, 0.0, "11/6", 11]);
        });
    });
    describe('addop -1, -1.0, 0/2, 0', function () {
        it('expected [0, -4.0, "1/3", 1]', function () {
            expect(invokeExecutionOn(jsmain, "-1i", "-1.0f", "0/2R", "0N_Foo")).to.eql([0, -4.0, "1/3", 1]);
        });
    });
});

describe('Subtraction', function () {
    const testopt = ["expression/bin_arith_ops", "subop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('subop 1, 3.0, 3/2, 10', function () {
        it('expected [0, 6.0, "7/6", 9]', function () {
            expect(invokeExecutionOn(jsmain, 1, 3.0, "3/2", 10)).to.eql([0, 6.0, "7/6", 9]);
        });
    });
    describe('subop -1, -1.0, 0/2, 2', function () {
        it('expected [-2, 2.0, "-1/3", 1]', function () {
            expect(invokeExecutionOn(jsmain, -1, -1.0, "0/2", 2)).to.eql([-2, 2.0, "-1/3", 1]);
        });
    });
    describe('subop underflow', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, -1, -1.0, "0/2", 0)).to.includes("arithmetic op underflow");
        });
    });
});

describe('Multiplication', function () {
    const testopt = ["expression/bin_arith_ops", "multop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('multop 0, 0.0, 0/2, 0', function () {
        it('expected [0, 0.0, "0", 0]', function () {
            expect(invokeExecutionOn(jsmain, 0, 0.0, "0/2", 0)).to.eql([0, 0.0, "0", 0]);
        });
    });
    describe('multop -1, -1.0, 3/2, 4', function () {
        it('expected [-2, 3.0, "3", 8]', function () {
            expect(invokeExecutionOn(jsmain, -1, -1.0, "3/2", 4)).to.eql([-2, 3.0, "3/4", 8]);
        });
    });
});

describe('Division', function () {
    const testopt = ["expression/bin_arith_ops", "divop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('divop 6, -3.0, 1/2, 2', function () {
        it('expected [1, 1.0, "1", 1]', function () {
            expect(invokeExecutionOn(jsmain, 6, -3.0, "1/2", 2)).to.eql([1, 1.0, "1", 1]);
        });
    });
    describe('divop 3, 1.0, 2/3, 4', function () {
        it('expected [2, -3.0, "4/3", 2]', function () {
            expect(invokeExecutionOn(jsmain, 3, 1.0, "2/3", 4)).to.eql([2, -3.0, "4/3", 2]);
        });
    });
    describe('divop zero int', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, 0, -3.0, "1/2", 2)).to.includes("division by 0");
        });
    });
    describe('divop zero float', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, 6, 0.0, "1/2", 2)).to.includes("division by 0");
        });
    });
});
