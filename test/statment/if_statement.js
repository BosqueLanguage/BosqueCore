"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('If statement basic', function () {
    const testopt = ["statement/if_statement", "simple"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(-3)', function () {
        it('expected 3', function () {
            expect(invokeExecutionOn(jsmain, -3)).to.eql(3);
        });
    });
    describe('process(5)', function () {
        it('expected 5', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(5);
        });
    });
});

describe('If statement ifelse', function () {
    const testopt = ["statement/if_statement", "ifelse"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(-1)', function () {
        it('expected "negative"', function () {
            expect(invokeExecutionOn(jsmain, -1)).to.eql("negative");
        });
    });
    describe('process(5)', function () {
        it('expected 5', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql("positive");
        });
    });
});

describe('If statement binder', function () {
    const testopt = ["statement/if_statement", "binder"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(none)', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql(0);
        });
    });
    describe('process(5)', function () {
        it('expected 4', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(4);
        });
    });
});

describe('If statement flow join', function () {
    const testopt = ["statement/if_statement", "fjoin"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(none)', function () {
        it('expected none', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql(null);
        });
    });
    describe('process(5)', function () {
        it('expected 6', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(6);
        });
    });
});
