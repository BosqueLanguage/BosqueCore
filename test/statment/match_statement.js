"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Match statement basic', function () {
    const testopt = ["statement/match_statement", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(1i)', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, ["Int", 1])).to.eql(1);
        });
    });
    describe('process(1n)', function () {
        it('expected 2', function () {
            expect(invokeExecutionOn(jsmain, ["Nat", 1])).to.eql(2);
        });
    });
    describe('process(1n)', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, ["None", null])).to.eql(0);
        });
    });
});

