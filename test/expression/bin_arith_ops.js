"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Addition', function () {
    const testopt = ["expression/bin_arith_ops", "addop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('addop 1i, 3.0f, 3/2R, 10I_Foo', function () {
        it('expected [2i, 0.0f, 11/6R, 11I_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "1i", "3.0f", "3/2R", "10I_Foo")).to.eql("[2i, 0.0f, 11/6R, 11I_Foo]");
        });
    });
    describe('addop -1i, -1.0f, 0/2R, 0I_Foo', function () {
        it('expected [0i, -4.0f, 1/3R, 1I_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "-1i", "-1.0f", "0/2R", "0I_Foo")).to.eql("[0i, -4.0f, 1/3R, 1I_Foo]");
        });
    });
});

describe('Subtraction', function () {
    const testopt = ["expression/bin_arith_ops", "subop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('subop 1i, 3.0f, 3/2R, 10N_Foo', function () {
        it('expected [0i, 6.0f, 7/6R, 9N_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "1i", "3.0f", "3/2R", "10N_Foo")).to.eql("[0i, 6.0f, 7/6R, 9N_Foo]");
        });
    });
    describe('subop -1i, -1.0f, 0/2R, 2N_Foo', function () {
        it('expected [-2i, 2.0f, -1/3R, 1N_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "-1i", "-1.0f", "0/2R", "2N_Foo")).to.eql("[-2i, 2.0f, -1/3R, 1N_Foo]");
        });
    });
    describe('subop underflow', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "-1i", "-1.0f", "0/2R", "0N_Foo")).to.includes("arithmetic op underflow");
        });
    });
});

describe('Multiplication', function () {
    const testopt = ["expression/bin_arith_ops", "multop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('multop 0i, 0.0f, 0/2R, 0N_Foo', function () {
        it('expected [0i, 0.0f, 0R, 0N_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "0i", "0.0f", "0/2R", "0N_Foo")).to.eql("[0i, 0.0f, 0R, 0N_Foo]");
        });
    });
    describe('multop -1i, -1.0f, 3/2R, 4N_Foo', function () {
        it('expected [-2i, 3.0f, 3R, 8N_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "-1i", "-1.0f", "3/2R", "4N_Foo")).to.eql("[-2i, 3.0f, 3/4R, 8N_Foo]");
        });
    });
});

describe('Division', function () {
    const testopt = ["expression/bin_arith_ops", "divop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('divop 6i, -3.0f, 1/2R, 2N_Foo', function () {
        it('expected [1i, 1.0f, 1R, 1N_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "6i", "-3.0f", "1/2R", "2N_Foo")).to.eql("[1i, 1.0f, 1R, 1N_Foo]");
        });
    });
    describe('divop 3i, 1.0f, 2/3R, 4N_Foo', function () {
        it('expected [2i, -3.0f, 4/3R, 2N_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "3i", "1.0f", "2/3R", "4N_Foo")).to.eql("[2i, -3.0f, 4/3R, 2N_Foo]");
        });
    });
    describe('divop zero int', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "0i", "-3.0f", "1/2R", "2N_Foo")).to.includes("division by 0");
        });
    });
    describe('divop zero float', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "6i", "0.0f", "1/2R", "2N_Foo")).to.includes("division by 0");
        });
    });
});
