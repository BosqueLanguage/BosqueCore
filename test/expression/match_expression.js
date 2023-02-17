"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Match Expression basic', function () {
    const testopt = ["expression/match_expression", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('match(none)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, ["None", null])).to.eql(0);
        });
    });
    describe('match(0i)', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, ["Int", 0])).to.eql(1);
        });
    });
    describe('match(7n)', function () {
        it('expected 2', function () {
            expect(invokeExecutionOn(jsmain, ["Nat", 7])).to.eql(2);
        });
    });
});

describe('Match Expression infer', function () {
    const testopt = ["expression/match_expression", "infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('match(none)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, ["None", null])).to.eql(["Int", 0]);
        });
    });
    describe('match(5)', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, ["Int", 5])).to.eql(["Int", 1]);
        });
    });
});

describe('Match Expression binder general', function () {
    const testopt = ["expression/match_expression", "binder"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('match(none)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, ["None", null])).to.eql(0);
        });
    });
    describe('match(5)', function () {
        it('expected 6', function () {
            expect(invokeExecutionOn(jsmain, ["Nat", 5])).to.eql(6);
        });
    });
});


describe('Match Expression binder option', function () {
    const testopt = ["expression/match_expression", "binder_option"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('match(nothing)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, ["Nothing", null])).to.eql(0);
        });
    });
    describe('match(something(5))', function () {
        it('expected 6', function () {
            expect(invokeExecutionOn(jsmain, ["Something<Nat>", 5])).to.eql(6);
        });
    });
});
