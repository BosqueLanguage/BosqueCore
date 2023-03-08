"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('If Expression Boolean Conditions -- simple x', function () {
    const testopt = ["expression/if_expression", "if_bool_x"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITE 0', function () {
        it('expected [0, 0]', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql([0, 0]);
        });
    });
    describe('ITE -1', function () {
        it('expected [1, -1]', function () {
            expect(invokeExecutionOn(jsmain, -1)).to.eql([1, -1]);
        });
    });
    describe('ITE 10', function () {
        it('expected [10, 1]', function () {
            expect(invokeExecutionOn(jsmain, 10)).to.eql([10, 1]);
        });
    });
});

describe('If Expression Boolean Conditions -- infer', function () {
    const testopt = ["expression/if_expression", "if_bool_infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITE 0', function () {
        it('expected null', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql(null);
        });
    });
    describe('ITE 10', function () {
        it('expected [0, 0.0, "0", 0]', function () {
            expect(invokeExecutionOn(jsmain, 10)).to.eql(10);
        });
    });
});

describe('If Expression ITest forms -- none variations', function () {
    const testopt = ["expression/if_expression", "if_itest_none"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITE 3', function () {
        it('expected [1, 1, 1]', function () {
            expect(invokeExecutionOn(jsmain, 3)).to.eql([1, 1, 1]);
        });
    });
    describe('ITE none', function () {
        it('expected [0, 0, 0]', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql([0, 0, 0]);
        });
    });
});


describe('If Expression ITest binds -- none variations', function () {
    const testopt = ["expression/if_expression", "if_itest_none_bind"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ITE 3', function () {
        it('expected [1, 1, 1]', function () {
            expect(invokeExecutionOn(jsmain, 3)).to.eql([3, 3]);
        });
    });
    describe('ITE none', function () {
        it('expected [0, 0, 0]', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql([0, 0]);
        });
    });
});
