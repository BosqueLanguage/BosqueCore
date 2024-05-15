"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Match statement basic', function () {
    const testopt = ["statement/match_statement", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(1i)', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "1i")).to.eql("1i");
        });
    });
    describe('process(1n)', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, "1n")).to.eql("2i");
        });
    });
    describe('process(none)', function () {
        it('expected 0i', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0i");
        });
    });
});

