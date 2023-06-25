"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('If statement basic', function () {
    const testopt = ["statement/if_statement", "simple"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(-3i)', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, "-3i")).to.eql("3i");
        });
    });
    describe('process(5)', function () {
        it('expected 5i', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql("5i");
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
            expect(invokeExecutionOn(jsmain, "-1i")).to.eql('"negative"');
        });
    });
    describe('process(5)', function () {
        it('expected "positive', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql('"positive"');
        });
    });
});

describe('If statement binder', function () {
    const testopt = ["statement/if_statement", "binder"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(none)', function () {
        it('expected 0i', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0i");
        });
    });
    describe('process(5i)', function () {
        it('expected 4i', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql("4i");
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
            expect(invokeExecutionOn(jsmain, "none")).to.eql("none");
        });
    });
    describe('process(5i)', function () {
        it('expected 6i', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql("6i");
        });
    });
});
