"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Method direct concept', function () {
    const testopt = ["expression/method_direct", "calls_concept"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('call Qux', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql([2, 4, 1, 1]);
        });
    });
    describe('call Qax', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql([2, 4, 1, 3]);
        });
    });
});

describe('Method direct union', function () {
    const testopt = ["expression/method_direct", "calls_union"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('call Qux', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql([2, 4, 1, 1]);
        });
    });
    describe('call Qax', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql([2, 4, 1, 3]);
        });
    });
});



