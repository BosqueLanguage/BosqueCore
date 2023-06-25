"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('If Expression Boolean Conditions -- simple x', function () {
    const testopt = ["expression/if_expression", "if_bool_x"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITE 0', function () {
        it('expected [0i, 0i]', function () {
            expect(invokeExecutionOn(jsmain, "0i")).to.eql("[0i, 0i]");
        });
    });
    describe('ITE -1', function () {
        it('expected [1i, -1i]', function () {
            expect(invokeExecutionOn(jsmain, "-1i")).to.eql("[1i, -1i]");
        });
    });
    describe('ITE 10', function () {
        it('expected [10i, 1i]', function () {
            expect(invokeExecutionOn(jsmain, "10i")).to.eql("[10i, 1i]");
        });
    });
});

describe('If Expression Boolean Conditions -- infer', function () {
    const testopt = ["expression/if_expression", "if_bool_infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITE 0', function () {
        it('expected none', function () {
            expect(invokeExecutionOn(jsmain, "0i")).to.eql("none");
        });
    });
    describe('ITE 10', function () {
        it('expected 10i', function () {
            expect(invokeExecutionOn(jsmain, "10i")).to.eql("10i");
        });
    });
});

describe('If Expression ITest forms -- none variations', function () {
    const testopt = ["expression/if_expression", "if_itest_none"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITE 3', function () {
        it('expected [1i, 1i, 1i]', function () {
            expect(invokeExecutionOn(jsmain, "3i")).to.eql("[1i, 1i, 1i]");
        });
    });
    describe('ITE none', function () {
        it('expected [0i, 0i, 0i]', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("[0i, 0i, 0i]");
        });
    });
});


describe('If Expression ITest binds -- none variations', function () {
    const testopt = ["expression/if_expression", "if_itest_none_bind"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITE 3', function () {
        it('expected [3i, 3i]', function () {
            expect(invokeExecutionOn(jsmain, "3i")).to.eql("[3i, 3i]");
        });
    });
    describe('ITE none', function () {
        it('expected [0i, 0i]', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("[0i, 0i]");
        });
    });
});
