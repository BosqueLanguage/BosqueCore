"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Logical /\\', function () {
    const testopt = ["expression/negation", "simpleneg"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Negate 1, 1.0, 3/2, 10', function () {
        it('expected [-1, -1.0, "-3/2", -10]', function () {
            expect(invokeExecutionOn(jsmain, 1, 1.0, "3/2", 10)).to.eql([-1, -1.0, "-3/2", -10]);
        });
    });
    describe('Negate -1, -1.0, -3/2, -10', function () {
        it('expected [1, 1.0, "3/2", 10]', function () {
            expect(invokeExecutionOn(jsmain, -1, -1.0, "-3/2", -10)).to.eql([1, 1.0, "3/2", 10]);
        });
    });
    describe('Negate 0, 0.0, 0/1, 0', function () {
        it('expected [0, 0.0, "0", 0]', function () {
            expect(invokeExecutionOn(jsmain, 0, 0.0, "0/2", 0)).to.eql([0, 0.0, "0", 0]);
        });
    });
});
