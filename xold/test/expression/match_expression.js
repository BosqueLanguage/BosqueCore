"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Match Expression basic', function () {
    const testopt = ["expression/match_expression", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('match(none)', function () {
        it('expected 0i,', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0i");
        });
    });
    describe('match(0i)', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "0i")).to.eql("1i");
        });
    });
    describe('match(7n)', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, "7n")).to.eql("2i");
        });
    });
});

describe('Match Expression infer', function () {
    const testopt = ["expression/match_expression", "infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('match(none)', function () {
        it('expected 0i,', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0i");
        });
    });
    describe('match(5i)', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql("1i");
        });
    });
});

describe('Match Expression binder general', function () {
    const testopt = ["expression/match_expression", "binder"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('match(none)', function () {
        it('expected 0n', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0n");
        });
    });
    describe('match(5n)', function () {
        it('expected 6n', function () {
            expect(invokeExecutionOn(jsmain, "5n")).to.eql("6n");
        });
    });
});


describe('Match Expression binder option', function () {
    const testopt = ["expression/match_expression", "binder_option"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('match(nothing)', function () {
        it('expected 0n,', function () {
            expect(invokeExecutionOn(jsmain, "nothing")).to.eql("0n");
        });
    });
    describe('match(something(5n))', function () {
        it('expected 6n', function () {
            expect(invokeExecutionOn(jsmain, "something(5n)")).to.eql("6n");
        });
    });
});
